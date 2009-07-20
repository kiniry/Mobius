//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
 /* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: Pog
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /*  09/26/2003 : Simplify integration achieved
 /******************************************************************************/
package jml2b.pog;

import jack.util.Logger;

import java.io.BufferedOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Enumeration;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LoadException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.QuantifiedForm;
import jml2b.formula.QuantifiedVarForm;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.languages.Languages;
import jml2b.pog.lemma.ExceptionalLemma;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.GoalOrigin;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.printers.ClassResolver;
import jml2b.pog.printers.IClassResolver;
import jml2b.pog.printers.IPrinter;
import jml2b.pog.proofobligation.ConstructorPO;
import jml2b.pog.proofobligation.MethodPO;
import jml2b.pog.proofobligation.ProofObligation;
import jml2b.pog.proofobligation.SourceProofObligation;
import jml2b.pog.proofobligation.StaticInitializationPO;
import jml2b.pog.proofobligation.WellDefinedInvPO;
import jml2b.pog.proofobligation.WellDefinedSpecPO;
import jml2b.pog.util.ColoredInfo;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Class;
import jml2b.structure.java.Constructor;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.Invariant;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import jml2b.structure.java.ModFlags;
import jml2b.structure.java.Package;
import jml2b.structure.java.Type;
import jml2b.structure.jml.Exsures;
import jml2b.structure.jml.JmlExpression;
import jml2b.structure.statement.BinaryExp;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.MethodCallExp;
import jml2b.structure.statement.MyToken;
import jml2b.structure.statement.StSequence;
import jml2b.structure.statement.StSkip;
import jml2b.structure.statement.StVarDecl;
import jml2b.structure.statement.Statement;
import jml2b.structure.statement.TerminalExp;
import jml2b.util.JpoOutputStream;
import jml2b.util.Profiler;
import jpov.JpoFile;

import org.eclipse.core.runtime.IProgressMonitor;

/**
 * This class provides static methods allowing to run the proof obligations
 * generation.
 * 
 * @author L. Burdy
 */
public class Pog extends Profiler
		implements
			JmlDeclParserTokenTypes,
			ModFlags,
			IFormToken {

	/**
	 * Returns the implicit part of a constructor corresponding to the
	 * initialization of the member fields.
	 * 
	 * @param fields
	 *            The set of fields of the current class
	 * @return the sequence of assignement of member field on instance
	 *         <code>this</code> with their initialization.
	 */
	static private Statement getMemberInitializer(Enumeration fields) {
		if (fields.hasMoreElements()) {
			Field f = (Field) fields.nextElement();
			if (!(f.getModifiers().isStatic()) && !(f.getModifiers().isModel())) {
				Expression e = f.getAssign();
				e.processIdent();
				e.instancie();
				return new StSequence(f, new BinaryExp(ASSIGN, new BinaryExp(
						DOT, new TerminalExp(LITERAL_this, "this"), ".",
						new TerminalExp(new Identifier(f))), "=", e),
						getMemberInitializer(fields));
			} else
				return getMemberInitializer(fields);
		} else
			return new StSkip();
	}

	/**
	 * Returns the implicit part of a constructor corresponding to the default
	 * initialization of the member fields.
	 * 
	 * @param fields
	 *            The set of fields of the current class
	 * @return the sequence of assignement of member field on instance
	 *         <code>this</code> with their initialization by default .
	 */
	static private Statement getMemberDefaultInitializer(Enumeration fields) {
		if (fields.hasMoreElements()) {
			Field f = (Field) fields.nextElement();
			if (!(f.getModifiers().isStatic()) && !(f.getModifiers().isModel())) {
				Expression e = f.getDefaultInitialiser();
				e.processIdent();
				e.instancie();
				return new StSequence(f, new BinaryExp(ASSIGN, new BinaryExp(
						DOT, new TerminalExp(LITERAL_this, "this"), ".",
						new TerminalExp(new Identifier(f))), "=", e),
						getMemberDefaultInitializer(fields));
			} else
				return getMemberDefaultInitializer(fields);
		} else
			return new StSkip();
	}

	/**
	 * Converts an enumeration of invariants into a conjunction.
	 * 
	 * @param invariants
	 *            The enumeration
	 * @return the expression corresponding to the conjunction of all the
	 *         element of the enumeration
	 */
	static private Expression invariantVector2Invariant(Enumeration invariants) {
		if (invariants.hasMoreElements()) {
			Invariant i = (Invariant) invariants.nextElement();
			return new BinaryExp(LOGICAL_OP, i.getInvariant(), "&&",
					invariantVector2Invariant(invariants));
		} else
			return new TerminalExp(MyToken.BTRUE, "(0=0)");
	}

	/**
	 * Quantifies and skolemizes the member invariant of a class for all
	 * instances of this class.
	 * 
	 * @param config
	 *            The current configuration
	 * @param c
	 *            The class
	 * @param i
	 *            The expression corresponding to a member invariant of the
	 *            class.
	 * @return a lemma corresponding to the member invariant where
	 *         <code>this</code> has been replaced with a free identifier:
	 *         <code>c_an_instance</code>.
	 * @throws PogException
	 */
	public static SimpleLemma declare(IJml2bConfiguration config, AClass c,
			Vector i) throws Jml2bException, PogException {
		TerminalExp var = new TerminalExp(new Identifier(c), "_an_instance");

		Vector prop = new Vector();
		Enumeration e = i.elements();
		while (e.hasMoreElements()) {
			JmlExpression je = (JmlExpression) e.nextElement();
			JmlExpression i1 = (JmlExpression) je.instancie().clone();
			i1 = i1.instancie(var);
			prop.add(i1);
		}

		SimpleLemma sl = new SimpleLemma(config, prop, new GoalOrigin(
				GoalOrigin.MEMBER_INVARIANT));
		sl.addImplicToGoal(declare(c), VirtualFormula.INVARIANT);
		sl.addImplicToGoal(new BinaryForm(B_IN, new TerminalForm(
				new Identifier(c), "_an_instance"), TerminalForm.$instances),
			VirtualFormula.INVARIANT);
		sl.addImplicToGoal(new BinaryForm(LOCAL_VAR_DECL, new TerminalForm(
				new Identifier(c), "_an_instance"), TerminalForm.$References),
			VirtualFormula.INVARIANT);
		return sl;

	}

	/**
	 * Returns the formula corresponding to the typing of a class instance
	 * <code>c_an_instance</code>.
	 * 
	 * @param c
	 *            The class
	 * @return <code>\typeof(c_an_instance) <: \type(c)</code>
	 */
	private static Formula declare(AClass c) {
		// \typeof(c_an_instance) <: \type(c)
		return new BinaryForm(Jm_IS_SUBTYPE, new BinaryForm(B_APPLICATION,
				TerminalForm.$typeof, new TerminalForm(new Identifier(c),
						"_an_instance")), new TTypeForm(IFormToken.Jm_T_TYPE,
				new Type(c)));
	}

	/**
	 * Quantifies the member invariant of a class for all instances of this
	 * class.
	 * 
	 * @param config
	 *            The current configuration
	 * @param c
	 *            The class
	 * @param i
	 *            The expression corresponding to a member invariant of the
	 *            class
	 * @return a formula corresponding to the member invariant quantified on
	 *         <code>c_an_instance</code> and where <code>this</code> has
	 *         been replaced with a free identifier: <code>c_an_instance</code>.
	 * @throws PogException
	 */
	public static FormulaWithSpecMethodDecl quantify(IJml2bConfiguration config, AClass c, Vector i)
			throws Jml2bException, PogException {
		TerminalExp var = new TerminalExp(new Identifier(c), "_an_instance");

		FormulaWithSpecMethodDecl prop = null;
		Enumeration e = i.elements();
		while (e.hasMoreElements()) {
			JmlExpression je = (JmlExpression) e.nextElement();
			JmlExpression i1 = (JmlExpression) je.instancie().clone();
			i1 = i1.instancie(var);
			FormulaWithSpecMethodDecl i2 = i1.predToForm(config);
			FormulaWithSpecMethodDecl prop1 = FormulaWithSpecMethodDecl.implies(declare(c), i2);
			FormulaWithSpecMethodDecl prop2 = FormulaWithSpecMethodDecl.implies(new BinaryForm(B_IN,
					(TerminalForm) var.exprToForm(config).getFormula(),
					TerminalForm.$instances), prop1);
			FormulaWithSpecMethodDecl prop3 = new FormulaWithSpecMethodDecl(prop2, new QuantifiedForm(Jm_FORALL,
					new QuantifiedVarForm(
							(TerminalForm) var.exprToForm(config).getFormula(),
							TerminalForm.$References), prop2.getFormula()));
			if (prop == null)
				prop = prop3;
			else
				prop = FormulaWithSpecMethodDecl.and(prop, prop3);
		}
		return prop;
	}

	/**
	 * Explicits the body of a constructor.
	 * <p>
	 * The body of a constructor should contains the following sequence :
	 * <p>
	 * &nbsp; default initialization of member fields
	 * </p>
	 * <p>
	 * &nbsp; call to super() (or this() if it is explicitly in the code)
	 * </p>
	 * <p>
	 * &nbsp; initialization of member fields
	 * </p>
	 * <p>
	 * &nbsp; body of the constructor (minus the call to a constructor if it is
	 * explicit)
	 * </p>
	 * </p>
	 * 
	 * @param config
	 *            The current configuration
	 * @param c
	 *            The constructor
	 * @param a
	 *            The class where the constructor is declared
	 * @return the explicit body of the constructor
	 */
	static private Statement constructor(IJml2bConfiguration config, Method c,
			Class a) throws Jml2bException, PogException {
		Expression e;
		Statement st_1;
		Statement firstStatement = c.getBody(config).firstStatement();
		if (firstStatement instanceof MethodCallExp
				&& ((MethodCallExp) firstStatement).getLeft().isDot()
				&& (e = (((BinaryExp) ((MethodCallExp) firstStatement)
						.getLeft()).getRight())) instanceof TerminalExp
				&& ((TerminalExp) e).getIdent() != null
				&& ((TerminalExp) e).getIdent().mth != null
				&& ((TerminalExp) e).getIdent().mth.isConstructor())
			st_1 = new StSequence(firstStatement, firstStatement,
					new StSequence(c,
							getMemberInitializer(a.fields.elements()), c
									.getBody(config).tail()));
		else {
			st_1 = new StSequence(c, new StSequence(c, new MethodCallExp(
					MyToken.METHOD_CALL, new BinaryExp(
							JmlDeclParserTokenTypes.DOT, new TerminalExp(
									LITERAL_this, "this"), ".",
							new TerminalExp(new Identifier(a
									.getSuperDefaultConstructor()))), "()",
					null), getMemberInitializer(a.fields.elements())), c
					.getBody(config));
		}
		return new StSequence(c, getMemberDefaultInitializer(a.fields
				.elements()), st_1);
	}

	/**
	 * Constructs the proof obligations associated with a set of classes
	 * 
	 * @param config
	 *            The current configuration
	 * @param classes
	 *            The set of classes
	 * @return the set of {@link ProofObligation}to calculate to obtain the
	 *         POs.
	 */
	protected static Vector generateProofObligations(IJml2bConfiguration config,
			Enumeration classes) throws Jml2bException, PogException {

		// Vector of ProofObligation containing all the POs of the current file.
		Vector lemmas = new Vector();

		int constructorCounter = 0;

		while (classes.hasMoreElements()) {

			Class a = (Class) classes.nextElement();

			// Accessible fields of all viewed classes.
			Vector accessibleFields = a.getAccessibleFields((JavaLoader) config.getPackage());

			// Static invariants of all viewed classes. Set of JmlExpression.
			Vector staticInvariant;

			// Member invariant of all viewed classes.
			FormulaWithSpecMethodDecl memberInvariant;
			
			// Pure method declarations of all viewed classes.
//			Formula pureMethodDecl;
			
//			if ((pureMethodDecl = a.getPureMethodDecl(config)) == null)
//				pureMethodDecl = new TerminalForm(B_BTRUE, "(0=0)");
			
			if ((staticInvariant = a.getGlobalStaticInvariant((JavaLoader) config.getPackage())) == null)
				staticInvariant = new Vector();
			if ((memberInvariant = a.getGlobalMemberInvariant(config)) == null)
				memberInvariant = new FormulaWithSpecMethodDecl(new TerminalForm(B_BTRUE, "(0=0)"));

			// Static + member invariants of all viewed classes.
			FormulaWithSpecMethodDecl globalInvariant = memberInvariant;
			Enumeration en = staticInvariant.elements();
			while (en.hasMoreElements()) {
				JmlExpression element = (JmlExpression) en.nextElement();
				globalInvariant = FormulaWithSpecMethodDecl.and(globalInvariant, element
						.predToForm(config));
			}
			globalInvariant.processIdent();

			SimpleLemma globalInvariantP = new SimpleLemma(config,
					staticInvariant,
					new GoalOrigin(GoalOrigin.STATIC_INVARIANT));
			globalInvariantP.addGoals(a.getGlobalMemberInvariantProof(config));

			SimpleLemma staticConstraintP = new SimpleLemma(config, a
					.getStaticConstraints(), new GoalOrigin(
					GoalOrigin.STATIC_CONSTRAINT));

			SimpleLemma instanceConstraintP = new SimpleLemma(config, a
					.getInstanceConstraints(), new GoalOrigin(
					GoalOrigin.INSTANCE_CONSTRAINT));

			//******************************************************************
			// Static Initialisation
			//******************************************************************
			Expression i = invariantVector2Invariant(a.staticInvariants
					.elements());
			Statement s = new StVarDecl(a.fields);
			// If the static initialization throws an exception, the invariant
			// has to be proven.
			Vector ex = new Vector();
			try {
				ex.add(new Exsures(new Type(((JavaLoader) config.getPackage()).getJavaLang()
						.getAndLoadClass(config, "Exception")), (String) null,
						i));
			} catch (Jml2bException e) {
				throw new PogException("Error loading Exception", s);
			}

			lemmas.add(new StaticInitializationPO(a, s, new Theorem(
					new SimpleLemma(config, i, new GoalOrigin(
							GoalOrigin.STATIC_INVARIANT))), new Theorem(config,
					ex.elements(), null, new GoalOrigin(GoalOrigin.EXSURES))));

			//******************************************************************
			// Invariant Well definedness
			//******************************************************************
			if (config.isWellDefPoGenerated()) {
				lemmas.add(new WellDefinedInvPO(config, a, a.getInvariants()));
				lemmas.add(new WellDefinedInvPO(config, a, a.getConstraints()));
			}

			if (!a.isInterface()) {
				//**************************************************************
				// Constructors
				//**************************************************************
				Enumeration e = a.constructors.elements();
				while (e.hasMoreElements()) {
					Constructor c = (Constructor) e.nextElement();
					if (c.getBody(config) != null) {

					c.completeModifiesWithOwnFields(config);

					Theorem p = new Theorem(config, c,
							(SimpleLemma) globalInvariantP.clone(),
							(SimpleLemma) staticConstraintP.clone(),
							new SimpleLemma(), accessibleFields);

					lemmas.add(new ConstructorPO(a, "Constructor_"
							+ constructorCounter++, c,  globalInvariant, c
							.getNormalizedRequires(config).predToForm(config),
							new ColoredInfo(c), constructor(config, c, a), p,
							new Theorem(new ExceptionalLemma(config, c,
									accessibleFields,
									(SimpleLemma) globalInvariantP.clone(),
									(SimpleLemma) staticConstraintP.clone(),
									new SimpleLemma()))));
					if (config.isWellDefPoGenerated())
						lemmas.add(new WellDefinedSpecPO(config, a, c));
					c.restore();
					}
				}

				//**************************************************************
				// Methods
				//**************************************************************
				e = a.methods.elements();
				while (e.hasMoreElements()) {
					Method c = (Method) e.nextElement();

					if (!c.hasNoCode()) {

						Theorem p = new Theorem(config, c,
								(SimpleLemma) globalInvariantP.clone(),
								(SimpleLemma) staticConstraintP.clone(),
								(SimpleLemma) instanceConstraintP.clone(),
								accessibleFields);

						lemmas
								.add(new MethodPO(
										a,
										c,
										globalInvariant,
										c.getNormalizedRequires(config)
												.predToForm(config),
										new ColoredInfo(c),
										c.getBody(config),
										p,
										new Theorem(
												new ExceptionalLemma(
														config,
														c,
														accessibleFields,
														(SimpleLemma) globalInvariantP
																.clone(),
														(SimpleLemma) staticConstraintP
																.clone(),
														(SimpleLemma) instanceConstraintP
																.clone()))));

					}
					if (config.isWellDefPoGenerated())
						lemmas.add(new WellDefinedSpecPO(config, a, c));
				}
			}
		}
		return lemmas;
	}

	/**
	 * Calculates the lemma to prove for the set of proof obligation and run the
	 * obvious prover if requested.
	 * 
	 * @param config
	 *            The current configuration
	 * @param proofObligations
	 *            The set of proof obligations
	 * @param obviousPo
	 *            The boolean indicating if the obvious prover must be ran
	 * @throws PogException
	 */
	private static void pog(IJml2bConfiguration config, Vector proofObligations,
			IProgressMonitor monitor) throws Jml2bException, PogException {
		PogException pe = null;
		Enumeration po = proofObligations.elements();
		while (po.hasMoreElements()) {
			ProofObligation p = (ProofObligation) po.nextElement();
			try {
				if (monitor != null) {
					if (monitor.isCanceled()) {
//						Package.clearAll();
						return;
					}
					monitor.subTask("Generating cases for "
							+ p.getDisplayedName());
				}
				p.pog(config);
				p.proveObvious(!config.isObviousPoGenerated());
			} catch (PogException pex) {
				if (pe == null)
					pe = pex;
			}
		}
		if (pe != null)
			throw pe;
	}

	/**
	 * Annotates all the fields that appear in the lemmas associated with a
	 * class to declare them in the Atelier B files.
	 * 
	 * @param c
	 *            The class
	 */
	private static void garbageIdent(Class c) {
		if (c.staticInitLemmas != null)
			c.staticInitLemmas.garbageIdent();
		if (c.wellDefInvLemmas != null)
			c.wellDefInvLemmas.garbageIdent();
		Enumeration e = c.getConstructors();
		while (e.hasMoreElements()) {
			Method element = (Method) e.nextElement();
			if (element.getLemmas() != null)
				element.getLemmas().garbageIdent();
			if (element.wellDefinednessLemmas != null)
				element.wellDefinednessLemmas.garbageIdent();
		}
		e = c.getMethods();
		while (e.hasMoreElements()) {
			Method element = (Method) e.nextElement();
			if (element.getLemmas() != null)
				element.getLemmas().garbageIdent();
			if (element.wellDefinednessLemmas != null)
				element.wellDefinednessLemmas.garbageIdent();
		}
	}

	/**
	 * Annotates all the fields that appear in the lemmas associated with a JML
	 * file to declare them in the Atelier B files.
	 * 
	 * @param c
	 *            The JML file
	 */
	public static void garbageIdent(JmlFile f) {
		Enumeration e = f.getClasses();
		while (e.hasMoreElements())
			garbageIdent((Class) e.nextElement());
	}

	/**
	 * Initalize the identifier array.
	 * 
	 * @param config
	 *            The current configuration
	 * @see IdentifierResolver#init(IJml2bConfiguration)
	 */
	public static void init(IJml2bConfiguration config) throws Jml2bException {
		// Initialize array of B name with arraylength.
		IdentifierResolver.init(config);
	}

	/**
	 * Generate the proof obligations associated with a JML file, calculate them
	 * and prove them with the obvious prover if requested. Saves them in a JPO
	 * file and writes the file .po and .pmi associated with the Atelier B.
	 * 
	 * @param file
	 *            The JML file
	 * @param config
	 *            The current configuration
	 * @throws PogException
	 * @throws IOException
	 */
	public void pog(JmlFile file, IJml2bConfiguration config,
			Vector addedDepends, Vector removedDepends, IProgressMonitor monitor)
			throws IOException, Jml2bException, PogException {

		SourceProofObligation.methodCount = 0;
		Statement.initFresh();

		// Initialize the exception classes.
		try {
			Package javalang = ((JavaLoader) config.getPackage()).getJavaLang();
			Statement.nullPointerException = javalang.getAndLoadClass(config,
				"NullPointerException");
			Statement.arrayIndexOutOfBoundsException = javalang
					.getAndLoadClass(config, "ArrayIndexOutOfBoundsException");
			Statement.arithmeticException = javalang.getAndLoadClass(config,
				"ArithmeticException");
			Statement.negativeArraySizeException = javalang.getAndLoadClass(
				config, "NegativeArraySizeException");
			Statement.classCastException = javalang.getAndLoadClass(config,
				"ClassCastException");
			Statement.arrayStoreException = javalang.getAndLoadClass(config,
				"ArrayStoreException");
		} catch (Jml2bException e) {
			throw new InternalError("Can't find Runtime Exceptions.");
		}

		try {
			Vector proofObligations = generateProofObligations(config, file
					.getClasses());
			if (monitor.isCanceled()) {
	//			Package.clearAll();
				return;
			}
			pog(config, proofObligations, monitor);
		} catch (OutOfMemoryError oome) {
			throw oome;
		}

		// Resolve B names.
		IdentifierResolver.resolveIdents();

		garbageIdent(file);

		ElementsForm.clearSuffix();

		ClassResolver printer = new ClassResolver((JavaLoader) config.getPackage());

		file.setDepends(printer.getJmlFiles());

		saveFiles(config, file, monitor, addedDepends, removedDepends, printer);

		IdentifierResolver.unResolveIdents();
	}

	public static void saveFiles(IJml2bConfiguration config, JmlFile file,
			IProgressMonitor monitor, Vector addedDepends,
			Vector removedDepends, IClassResolver printer) throws IOException {
		File fjpo = new File(config.getSubdirectory(), file.getFlatName( config.getPackage())
				+ ".jpo");
		File fjpop = new File(config.getSubdirectory(), file.getFlatName( config.getPackage())
				+ ".jpop");
		if (fjpo.exists() && fjpop.exists()) {
			DataInputStream ostr_jpo = null;
			DataInputStream ostr_jpop = null;
			try {
				if (monitor != null)
					monitor.subTask("Merging");
				JpoFile jpoF = new JpoFile(config, file.getFlatName(config.getPackage()));
				jpov.structure.JmlFile merged = jpoF.getJmlFile();

				Enumeration e = file.getDepends().elements();
				while (e.hasMoreElements()) {
					String element = (String) e.nextElement();
					if (!merged.dependsContains(element)) {
						addedDepends.add(element);
					}
				}
				for (int i = 0; i < merged.getDepends().length; i++) {
					String element = merged.getDepends()[i];
					if (file.getDepends().indexOf(element) == -1) {
						removedDepends.add(element);
					}
				}
				if (addedDepends.size() == 0 && removedDepends.size() == 0)
					file.mergeWith(merged);

				jpoF.close();

			} catch (LoadException e) {
				Logger.err.println("LoadException " + e.toString() + "\n" +
						file.getFlatName(config.getPackage()) + ".jpo is ignored");
				addedDepends.addAll(file.getDepends());
			} catch (IOException e) {
				Logger.err.println("    " + e.toString());
				Logger.err.println(file.getFlatName(config.getPackage()) + ".jpo is ignored");
				addedDepends.addAll(file.getDepends());
			} finally {
				if (ostr_jpo != null)
					ostr_jpo.close();
				if (ostr_jpop != null)
					ostr_jpop.close();
			}
		} else {
			addedDepends.addAll(file.getDepends());
		}

		Enumeration e = Languages.getLanguagesNames();
		while (e.hasMoreElements()) {
			String name = (String) e.nextElement();
			IPrinter ip = Languages.getPrinterClass(name);
			if (ip != null && config.isObviousProver(name)) {
				if (monitor != null)
					monitor.subTask("Proving");
				writeJpo(config, file, fjpo, fjpop);
				ip.print(config, printer, file, config.getSubdirectory());
				IObviousProver iop = Languages.getObviousProverClass(name);
				iop.prove(config, file);
				file.purgeObvious();
			}
		}

		e = Languages.getLanguagesNames();
		while (e.hasMoreElements()) {
			String name = (String) e.nextElement();
			IPrinter ip = Languages.getPrinterClass(name);
			if (ip != null && config.isFileGenerated(name)) {
				if (monitor != null)
					monitor.subTask("Writing " + name + " output file");
				ip.print(config, printer, file, config.getSubdirectory());
			}
		}
		if (monitor != null)
			monitor.subTask("Writing jpo file");
		writeJpo(config, file, fjpo, fjpop);
	}

	private static void writeJpo(IJml2bConfiguration config, JmlFile file, File fjpo, File fjpop)
			throws IOException {
		JpoOutputStream stream = new JpoOutputStream(new BufferedOutputStream(
				new FileOutputStream(fjpo)));
		file.save(config, stream);
		stream.close();

		DataOutputStream dstr = new DataOutputStream(new BufferedOutputStream(
				new FileOutputStream(fjpop)));
		stream.save(dstr);
		dstr.close();
	}

	/**
	 * Clear the names in the identifier array.
	 * 
	 * @see IdentifierResolver#clearName()
	 */
	public static void end() {
		IdentifierResolver.clearName();
	}

	/**
	 * Generates the proof obligations for all the JML files, calculate them and
	 * prove them with the obvious prover if requested. Saves them in a JPO file
	 * and writes the file .po and .pmi associated with the Atelier B.
	 * 
	 * @param files
	 *            The array of JML files
	 * @param config
	 *            The current configuration
	 * @throws PogException
	 * @throws IOException
	 */
	public void pog(JmlFile files[], IJml2bConfiguration config)
			throws IOException, Jml2bException, PogException {
		int i;

		init(config);
		for (i = 0; i < files.length; i++) {
			pog(files[i], config, new Vector(), new Vector(), null);
		}
		end();
	}

}