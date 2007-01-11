//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SpecCase.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.jml;

import java.io.Serializable;
import java.util.Enumeration;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LinkException;
import jml2b.exceptions.ParseException;
import jml2b.exceptions.PogException;
import jml2b.exceptions.TokenException;
import jml2b.exceptions.TypeCheckException;
import jml2b.formula.ElementsForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkUtils;
import jml2b.link.Linkable;
import jml2b.link.TypeCheckable;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.structure.AField;
import jml2b.structure.java.Class;
import jml2b.structure.java.IModifiers;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ModFlags;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.BinaryExp;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.MyToken;
import jml2b.structure.statement.TerminalExp;
import antlr.collections.AST;

/**
 * This class implements a specification case, that is a labelled record of 
 * requires, modifies, ensures and exsures.
 * @author L. Burdy, A. Requet
 */
public class SpecCase
	extends ParsedItem
	implements Linkable, TypeCheckable, Serializable, JmlDeclParserTokenTypes {

	/**
	 * Constant corresponding to lightweight cases.
	 */
	public static final int LIGHTWEIGHT_CASE = 0;

	/**
	 * Constant corresponding to normal behavior cases.
	 */
	public static final int NORMAL_BEHAVIOR_CASE = 1;

	/**
	 * Constant corresponding to exceptional_behavior cases.
	 */
	public static final int EXCEPTIONAL_BEHAVIOR_CASE = 2;

	/**
	 * Constant corresponding to default behavior cases.
	 */
	public static final int DEFAULT_BEHAVIOR_CASE = 3;

	/**
	 * Collects all the indentifier of the exsures clause to give them an index 
	 * in the identifer array. This array is then analyzed to give short name 
	 * when it is possible to identifiers.
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	public static void exsureVectorProcessIdent(Enumeration ex) {
		while (ex.hasMoreElements())
			 ((Exsures) ex.nextElement()).processIdent();
	}

	/**
	 * Instancie the exsures clause.
	 * More <a href="{@docRoot}/jml2b/structure/java/doc-files/instancie.html"> 
	 * informations</a> on instancie.
	 **/
	public static void exsureVectorInstancie(Enumeration ex) {
		while (ex.hasMoreElements())
			 ((Exsures) ex.nextElement()).instancie();
	}

	public static void exsureVectorRenameParam(
		Enumeration ex,
		Parameters signature,
		Parameters newSignature) {
		while (ex.hasMoreElements())
			 ((Exsures) ex.nextElement()).renameParam(signature, newSignature);

	}

	/**
	 * Parses the label clause of a specification case.
	 * @param labels The set of labels to constructs
	 * @param a The currently parsed AST tree
	 * @param jmlFile The currently parsed JML file
	 * @throws Jml2bException
	 */
	public static void parseLabel(Vector labels, AST a, JmlFile jmlFile)
		throws Jml2bException {
		if (a.getType() != LABEL_KEYWORD) {
			throw new TokenException(
				jmlFile,
				(LineAST) a,
				"SpecCase.parseLabel",
				"LABEL_KEYWORD",
				a.getType());
		}
		AST child = a.getFirstChild();
		Expression s = Expression.createE(jmlFile, child);
		s.parse(child);
		labels.add(s);
	}

	/**
	 * Labels associated with this spec case.
	 * Labels are @see Expression.
	 */
	private Vector labels;

	/** 
	 * Content of the requires clause for this spec case.
	 */
	private Expression requires;

	/**
	 * Content of the ensures clause for this spec case.
	 */
	private Expression ensures;

	/**
	 * Vector holding the content of the exsures clause for this spec case.
	 * All the elements of this vector are of type <code>Exsures</code>
	 */
	private Vector exsure;

	/*@ 
	  @ private invariant labels != null
	  @                && requires != null
	  @                && ensures != null
	  @                && exsure != null
	  @                && labels.elementType <; \type(Expression)
	  @                && exsure.elementType <: \type(Exsures);
	  @*/

	/**
	 * Content of the modifies clause. It can be <code>null</code>
	 */
	private ModifiesClause modifies;

	/**
	 * Visibility modifiers associated to this spec case. 
	 * It can be <code>null</code>
	 */
	private IModifiers modifiers;

	//	/**
	//	 * Construct an empty spec case from parsed informations.
	//	 * @param req The requires clause. It can be <code>null</code>
	//	 * @param labels The labels associated with this case
	//	 * @param mods The modifiers
	//	 * @param type The type
	//	 **/
	//	/*@
	//	  @ requires type == NORMAL_BEHAVIOR_CASE ||
	//	  @          type == EXCEPTIONAL_BEHAVIOR_CASE ||
	//	  @          type == DEFAULT_BEHAVIOR_CASE ||
	//	  @          type == LIGHTWEIGHT_CASE;
	//	  @ requires labels != null && labels.elementType <: \type(Expression);
	//	  @*/
	//	public SpecCase(
	//		IJml2bConfiguration config,
	//		Expression req,
	//		Vector labels,
	//		Modifiers mods,
	//		int type)
	//		throws Jml2bException {
	//		requires = req != null ? req : config.getDefaultRequires();
	//
	//		this.labels = labels;
	//
	//		// ensures is initialised to default in all cases, excepted for
	//		// EXCEPTIONAL_BEHAVIOR cases
	//		ensures =
	//			(type != EXCEPTIONAL_BEHAVIOR_CASE)
	//				? config.getDefaultEnsures()
	//				: new TerminalExp(LITERAL_false, "FALSE");
	//
	//		// exsures is initialised to empty,
	//		exsure = new Vector();
	//
	//		// add (Exception) false; to the list of exsures in the case
	//		// of normal behavior specification.
	//		if (type == NORMAL_BEHAVIOR_CASE) {
	//			addUnlinkedExsuresFalse("java.lang.Exception");
	//		} else
	//			addDefaultExsures(config);
	//
	//		modifies = config.getDefaultModifies();
	//		modifiers = mods;
	//	}

	public SpecCase(IJml2bConfiguration config, IModifiers mods)
		throws Jml2bException {
		labels = new Vector();
		requires = config.getDefaultRequires();
		ensures = config.getDefaultEnsures();
		exsure = config.getDefaultExsures();
		if (mods.isPure())
			modifies = new ModifiesNothing();
		else
			modifies = config.getDefaultModifies();
		modifiers = null;
		modifiers = mods;
	}

	/**
	 * Construct an empty spec case.
	 **/
	public SpecCase(IJml2bConfiguration config) {
		labels = new Vector();
		requires = config.getDefaultRequires();
		ensures = config.getDefaultEnsures();
		exsure = config.getDefaultExsures();
		modifies = config.getDefaultModifies();
		modifiers = null;
	}

	public SpecCase() {
		labels = new Vector();
		exsure = new Vector();
	}

	/**
	 * Construct and link an empty by default spec case.
	 * @param config The current configuration
	 * @param f The current link context
	 **/
	public SpecCase(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		labels = new Vector();
		requires = config.getDefaultRequires();
		requires.link(config, f);
		ensures = config.getDefaultEnsures();
		ensures.link(config, f);
		exsure = config.getDefaultExsures();
		LinkUtils.linkEnumeration(config, exsure.elements(), f);
		if (f.currentMethod.getModifiers().isPure())
			modifies = new ModifiesNothing();
		else
			modifies = config.getDefaultModifies();
		modifiers = null;
	}

	public SpecCase(Expression ens, ModifiesClause mod) {
		labels = new Vector();
		requires = new TerminalExp(MyToken.BTRUE, "(0=0)");
		if (ens != null) {
			ensures = ens;
		} else
			ensures = new TerminalExp(MyToken.BTRUE, "(0=0)");
		if (mod == null)
			modifies = new ModifiesNothing();
		else {
			modifies = mod;
		}
	}

	public Object clone() {
		SpecCase res = new SpecCase();
		res.labels = labels;
		res.requires = (Expression) requires.clone();
		res.ensures = (Expression) ensures.clone();
		res.exsure = new Vector();
		Enumeration e = exsure.elements();
		while (e.hasMoreElements()) {
			Exsures element = (Exsures) e.nextElement();
			res.exsure.add(element.clone());
		}
		res.modifies = (ModifiesClause) modifies.clone();
		return res;
	}

	/**
	 * Parses the content of a lightweight spec case. The spec case is assumed
	 * not to contain subcases.
	 */
	//@ requires tree.getType() == SPEC_CASE;
	public AST parseSpecBlock(JmlFile file, AST tree) throws Jml2bException {
		AST current = tree;
		loop : while (current != null) {
			switch (current.getType()) {
				case REQUIRES_KEYWORD :
					requires =
						Expression.createE(file, current.getFirstChild());
					requires.parse(current.getFirstChild());
					break;
				case SIG_SEQ :
					parseExsures(file, current.getFirstChild(), 0);
					break;
				case ENS_SEQ :
					parseEnsures(file, current.getFirstChild(), 0);
					break;
				case ASGNABLE_SEQ :
					// modifies
					parseModifies(file, current.getFirstChild(), 0);
					break;
				case CONT_SEQ :
				case BREAKS_SEQ :
				case RETURNS_SEQ :
				case DIV_SEQ :
					// currently ignored
					break;
				default :
					break loop;
			}

			current = current.getNextSibling();
		}
		//		if (!hasExsures()) {
		//			addUnlinkedExsuresFalse("java.lang.Exception");
		//		}
		//		completeModifies();
		return current;
	}

	/**
	 * Return true if the current spec case has an exsure clause defined.
	 */
	public boolean hasExsures() {
		return !exsure.isEmpty();
	}

	/**
	 * Completes the modifies, if no modifies were declared, the modifies
	 * becomes a <code>modifies \everything</code>
	 **/
	public void completeSpecCase(
		IJml2bConfiguration config,
		Expression req,
		Vector labels,
		IModifiers mods,
		IModifiers methodMods,
		int type)
		throws Jml2bException {
		requires = req != null ? req : config.getDefaultRequires();

		this.labels = labels;

		// ensures is initialised to default in all cases, excepted for
		// EXCEPTIONAL_BEHAVIOR cases
		if (ensures == null)
			ensures =
				(type != EXCEPTIONAL_BEHAVIOR_CASE)
					? config.getDefaultEnsures()
					: new TerminalExp(LITERAL_false, "FALSE");

		if (exsure.size() == 0) {
			// add (Exception) false; to the list of exsures in the case
			// of normal behavior specification.
			if (type == NORMAL_BEHAVIOR_CASE) {
				addUnlinkedExsuresFalse("java.lang.Exception");
			} else
				exsure = config.getDefaultExsures();
		}

		if (modifies == null)
			if (methodMods != null && methodMods.isPure())
				modifies = new ModifiesNothing();
			else
				modifies = config.getDefaultModifies();

		modifiers = mods;
	}

	/**
	 * Add a exsure false clause for the given exception type <code>fqn</code>.
	 * This method should be called before the SpecCase is linked, since it
	 * adds unlinked elements.
	 * <p>
	 * @param fqn the fully qualified name of the exception type.
	 */
	public void addUnlinkedExsuresFalse(String fqn) {
		Type t = Type.createUnlinkedClass(fqn);
		Exsures e =
			new Exsures(
				t,
				(String) null,
				new TerminalExp(LITERAL_false, "FALSE"));
		exsure.add(e);
	}

	//	/**
	//	 * Add an exsure false clause for the given exception type <code>fqn</code>.
	//	 * <code>fqn</code> should already be loaded when this method is called.
	//	 */
	//	public void addExsuresFalse(IJml2bConfiguration config, String fqn)
	//		throws Jml2bException {
	//		Class c = JmlLoader.loadClass(config, fqn);
	//		Type t = new Type(c);
	//		Exsures e =
	//			new Exsures(
	//				t,
	//				(String) null,
	//				new TerminalExp(LITERAL_false, "FALSE"));
	//		exsure.add(e);
	//	}

	/**
	 * @see jml2b.link.Linkable#link(IJml2bConfiguration, LinkContext)
	 */
	public void link(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		if (requires != null) {
			requires.link(config, f);
		}
		if (ensures != null) {
			ensures.link(config, f);
		}
		LinkUtils.linkEnumeration(config, exsure.elements(), f);

		// no link operation for modifies
	}

	/**
	 * @see jml2b.link.Linkable#linkStatements(IJml2bConfiguration, LinkContext)
	 */
	public int linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		if (requires != null) {
			requires.linkStatements(config, f);
		}
		if (ensures != null) {
			f.setResultAdmitted(true);
			ensures.linkStatements(config, f);
			f.setResultAdmitted(false);
		}
		LinkUtils.linkStatements(config, exsure.elements(), f);
		if (modifies != null) {
			modifies.linkStatements(config, f);
			if (( f.currentMethod.getModifiers()).isPure()
				&& !(modifies instanceof ModifiesNothing))
				throw new LinkException(
					"Pure methods cannot have a modifies clause different from \\nothing",
					f.currentMethod);
		}
		return 0;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		if (requires != null) {
			Type t = requires.typeCheck(config, f);
			if (!t.isBoolean())
				throw new TypeCheckException(
					"A requires clause should contain a boolean and not a "
						+ t.toJava(),
					this);
		}
		if (ensures != null) {
			Type t = ensures.typeCheck(config, f);
			if (!t.isBoolean())
				throw new TypeCheckException(
					"An ensures clause should contain a boolean and not a "
						+ t.toJava(),
					this);
		}
		LinkUtils.typeCheckEnumeration(config, exsure.elements(), f);
		if (modifies != null) {
			modifies.typeCheck(config, f);
		}
		return null;
	}

	/**
	 * Parse the content of an exsures clause, returning the new value for 
	 * <code>first_line</code>.
	 */
	public int parseExsures(JmlFile jmlFile, AST a, int first_line)
		throws Jml2bException {
		return Exsures.parseExsures(jmlFile, a, first_line, exsure);
	}

	/** 
	 * Parses the content of the ensures clause, and returns the new value
	 * for <code>first_line</code>.
	 */
	public int parseEnsures(JmlFile jmlFile, AST a, int first_line)
		throws Jml2bException {
		while (a != null) {
			if (a.getType() != ENSURES_KEYWORD) {
				throw new TokenException(
					jmlFile,
					(LineAST) a,
					"Method.parseEnsures",
					"ENSURES_KEYWORD",
					a.getType());
			}
			if (a instanceof LineAST && ((LineAST) a).line < first_line)
				first_line = ((LineAST) a).line;

			AST child = a.getFirstChild();
			Expression s = Expression.createE(jmlFile, child);
			s.parse(child);
			if (ensures == null)
				ensures = s;
			else
				ensures = new BinaryExp(LOGICAL_OP, ensures, "&&", s);
			
			a = a.getNextSibling();
		}
		return first_line;
	}

	/**
	 * Parses the modifies clause, and returns the updated value of 
	 * <code>first_line</code>.
	 */
	public int parseModifies(JmlFile jmlFile, AST a, int first_line)
		throws Jml2bException {
		while (a != null) {
			switch (a.getType()) {
				case ASSIGNABLE_KEYWORD :
					if (a instanceof LineAST
						&& ((LineAST) a).line < first_line)
						first_line = ((LineAST) a).line;
					ModifiesClause tmp =
						ModifiesClause.create(jmlFile, a.getFirstChild());
					if (tmp != null)
						if (modifies == null) {
							modifies = tmp;
						} else {
							try {
								((ModifiesList) modifies).add(
									(ModifiesList) tmp);
							} catch (ClassCastException cce) {
								throw new ParseException(
									jmlFile,
									(LineAST) a,
									"Invalid modifies clause");
							}
						}
					break;
				default :
					throw new TokenException(
						jmlFile,
						(LineAST) a,
						"Modifies.parse",
						"ASSIGNABLE_KEYWORD",
						a.getType());
			}
			a = a.getNextSibling();
		}
		return first_line;
	}

	/**
	 * Normalize the specification case.
	 * Ensures that <code>processIdent</code> and <code>instancie</code> are 
	 * called for each of the clause.
	 * If no modifies is set, set it to <code>\modifieseverything</code>.
	 * Adds the dependees to the modifies list.
	 */
	public void jmlNormalize(IJml2bConfiguration config, Class definingClass)
		throws PogException {
		requires.processIdent();
		requires = (Expression) requires.instancie();

		ensures.processIdent();
		ensures = (Expression) ensures.instancie();

		exsureVectorProcessIdent(exsure.elements());
		exsureVectorInstancie(exsure.elements());

		if (modifies == null) {
			modifies = new ModifiesEverything();
		} else {
			modifies.processIdent();

			modifies.instancie(config);
			modifies.addDepends(config, definingClass);
		}
	}

	public void renameParam(
		IJml2bConfiguration config,
		Parameters signature,
		Parameters newSignature)
		throws PogException {
		requires = requires.renameParam(signature, newSignature);
		ensures = ensures.renameParam(signature, newSignature);
		exsureVectorRenameParam(exsure.elements(), signature, newSignature);
		modifies.renameParam(config, signature, newSignature.signature);
	}
	/**
	 * Complete the modifies clause of a constructor with the fields of the
	 * class.
	 * @param l
	 **/
	public void completeModifiesWithOwnFields(ModifiesList l) {
		modifies = modifies.completeModifiesWithFields(l);
	}

	/**
	 * Returns the Java informations corresponding to this case
	 * @return a string to be displayed as tooltip text in the viewer.
	 **/
	public String getInfo() {
		String res = "\n requires " + requires.toJava(10) + ";";
		res += "\n modifies " + modifies.toJava(10) + ";";
		res += "\n ensures " + ensures.toJava(9) + ";";
		Enumeration e = exsure.elements();
		while (e.hasMoreElements()) {
			Exsures ex = (Exsures) e.nextElement();
			res += "\n exsures " + ex.toJava(9);
		}
		return res;
	}

	/**
	 * Returns the ensures clause guarded by the requires clause
	 **/
	public Expression getNormalizedEnsures() {
		Expression res = getEnsures();
		Expression r = getRequires();
		if (!(r.isBTrue() || getEnsures().isBTrue()))
			res = new BinaryExp(IMPLICATION_OP, r, "==>", res);
		return res;
	}

	public Expression getExsuresAsExpression() {
		Expression res = null;
		Enumeration e = getExsures();
		while (e.hasMoreElements()) {
			Exsures sc = (Exsures) e.nextElement();
			Expression tmp = sc.getNormalized();
			if (res == null)
				res = tmp;
			else
				res = new BinaryExp(LOGICAL_OP, res, "||", tmp);
		}
		if (res == null)
			res = new TerminalExp(MyToken.BTRUE, "(0=0)");
		Expression r = getRequires();
		if (!(r.isBTrue() || res.isBTrue()))
			res = new BinaryExp(IMPLICATION_OP, r, "==>", res);
		return res;
	}

	/**
	 * Returns the lemmas concerning the proof of the modifies clause.
	 * @param config The current configuration
	 * @param fields The set of modifiable fields
	 * @throws PogException
	 **/
	public SimpleLemma modifiesLemmas(
		IJml2bConfiguration config,
		Vector fields)
		throws PogException {
		Vector nonModifiedFields = new Vector();
		Enumeration e = fields.elements();
		while (e.hasMoreElements()) {
			AField f = (AField) e.nextElement();
			Formula fo = new TerminalForm(new Identifier(f));
			fo.processIdent();
			Formula oldF = new UnaryForm(IFormToken.Jm_T_OLD, fo);
			nonModifiedFields.add(oldF);
		}
		Formula[] nonModifiedElements =
			new Formula[ElementsForm.elements.length];
		for (int i = 0; i < ElementsForm.elements.length; i++) {
			nonModifiedElements[i] =
				new UnaryForm(IFormToken.Jm_T_OLD, ElementsForm.elements[i]);
		}
		return modifies.modifiesLemmas(
			config,
			fields,
			nonModifiedFields,
			nonModifiedElements);
	}

	/**
	 * Returns the labels.
	 * @return Vector
	 */
	public Vector getLabels() {
		return labels;
	}

	/**
	 * Returns the content of the ensures clause.
	 */
	public Expression getEnsures() {
		return ensures;
	}

	/**
	 * Returns an <code>Enumeration</code> enumerating the content of the 
	 * exsures clause.
	 * The elements returned by the <code>Enumeration</code> object will be
	 * of type <code>Exsures</code>.
	 */
	public Enumeration getExsures() {
		return exsure.elements();
	}

	/**
	 * Returns the content of the requires clause.
	 */
	public Expression getRequires() {
		return requires;
	}

	/**
	* Returns the content of the modifies clause.
	*/
	public ModifiesClause getModifies() {
		return modifies;
	}

	/**
	 * Returns the modifier associated to this <code>SpecCase</code>.
	 * Returns <code>null</code> if no modifier is available.
	 */
	public IModifiers getModifiers() {
		return modifiers;
	}

	/**
	 * Sets the modifiers for the current <code>SpecCase</code> object.
	 */
	public void setModifiers(Modifiers mods) {
		modifiers = mods;
	}

	public String emit(IJml2bConfiguration config) {
		String s = "";
		if (!requires.equals(config.getDefaultRequires()))
			s += "       requires " + requires.toJava(16) + ";\n";
		if (!modifies.equals(config.getDefaultModifies()))
			s += "       modifies " + modifies.toJava(16) + ";\n";
		if (!ensures.equals(config.getDefaultEnsures()))
			s += "       ensures " + ensures.toJava(15) + ";\n";
		if (!exsuresEquals(exsure.elements(),
			config.getDefaultExsures().elements())) {
			Enumeration e = exsure.elements();
			while (e.hasMoreElements()) {
				Exsures element = (Exsures) e.nextElement();
				s += "       exsures " + element.emit() + ";\n";
			}
		}
		return s;
	}

	/**
	 * @param vector
	 * @return
	 */
	private static boolean exsuresEquals(Enumeration v1, Enumeration v2) {
		if (v1.hasMoreElements()) {
			if (v2.hasMoreElements()) {
				return ((Exsures) v1.nextElement()).equals(
					(Exsures) v2.nextElement())
					&& exsuresEquals(v1, v2);
			} else
				return false;
		}
		return !v2.hasMoreElements();
	}

	public void setParsedItem(ParsedItem pi) {
		ensures.setParsedItem(pi);
		requires.setParsedItem(pi);
		if (modifies != null)
			modifies.setParsedItem(pi);
		Enumeration e = exsure.elements();
		while (e.hasMoreElements()) {
			Exsures ex = (Exsures) e.nextElement();
			ex.setParsedItem(pi);
		}
	}

	static final long serialVersionUID = -6982092608895645311L;

	public void addAnnotation(IJml2bConfiguration config, SpecCase sc) {
		if (modifies instanceof ModifiesNothing)
			modifies = sc.modifies;
		else if (modifies instanceof ModifiesList) {
			if (sc.modifies instanceof ModifiesEverything)
				modifies = sc.modifies;
			else if (sc.modifies instanceof ModifiesList)
				((ModifiesList) modifies).addWithoutDoublon(
					config,
					(ModifiesList) sc.modifies);
		}
		if (ensures.isBTrue())
			ensures = sc.ensures;
		else if (!sc.ensures.isBTrue())
			ensures = ensures.addInConjonction(sc.ensures);
	}

	public boolean addAnnotation(
		IJml2bConfiguration config,
		Expression ens,
		ModifiesClause mod) {
		boolean added = false;
		if (mod != null)
			if (modifies instanceof ModifiesNothing) {
				modifies = mod;
				added = true;
			} else if (modifies instanceof ModifiesList) {
				added =
					((ModifiesList) modifies).addWithoutDoublon(
						config,
						(ModifiesList) mod);
			}
		if (ens != null)
			if (ensures.isBTrue()) {
				ensures = ens;
				added = true;
			} else {
				Expression newEnsures = ensures.addInConjonction(ens);
				if (newEnsures != ensures) {
					ensures = newEnsures;
					added = true;
				}
			}
		return added;
	}

	public boolean addComputedModifies(
		IJml2bConfiguration config,
		ModifiesList ml) {
		if (modifies instanceof ModifiesNothing) {
			modifies = ml;
			return true;
		} else if (modifies instanceof ModifiesList) {
			return ((ModifiesList) modifies).addWithoutDoublon(config, ml);
		}
		return false;
	}

	/**
	 * @param expression
	 */
	public void setEnsures(Expression expression) {
		ensures = expression;
	}

	/**
	 * @param vector
	 */
	public void setExsure(Vector vector) {
		exsure = vector;
	}

	/**
	 * @param clause
	 */
	public void setModifies(ModifiesClause clause) {
		modifies = clause;
	}

	/**
	 * @param expression
	 */
	public void setRequires(Expression expression) {
		requires = expression;
	}

}
