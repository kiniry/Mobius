//******************************************************************************
/* Copyright (c) 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SimplyPrinter
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package simplifyPlugin;

import jack.util.Logger;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.LanguageException;
import jml2b.pog.lemma.NonObviousGoal;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.printers.AClassEnumeration;
import jml2b.pog.printers.IClassResolver;
import jml2b.pog.printers.IPrinter;
import jml2b.structure.AField;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import jml2b.structure.java.Type;

/**
 * @author Antoine Requet <antoine.requet@gemplus.com>
 * @author L. Burdy
 */
public class SimplifyPrinter implements IPrinter {

	IClassResolver printer;

	PrintStream stream;

	OutputStream ostream;

	JmlFile fi;
	File output_directory;

	boolean firstItem;

	//	public SimplifyPrinter(PrintStream ps) {
	//		super(ps);
	//	}
	//
	//	public SimplifyPrinter(FilePrinter fp, PrintStream ps) {
	//		super(fp, ps);
	//	}

	public Enumeration getClassesAndInterfacesEnumeration() {
		return new SequenceEnumeration(
			printer.getClasses(),
			printer.getInterfaces());
	}

	public void printClasses(IJml2bConfiguration config) {

		stream.println("(BG_PUSH (AND");
		// define all the classes as distinct elements
		stream.println("(DISTINCT ");
		// print builtin types
		for (int i = 0; i < builtinNames.length; ++i) {
			stream.println("   " + builtinNames[i]);
		}

		Enumeration e = getClassesAndInterfacesEnumeration();

		while (e.hasMoreElements()) {
			AClass c =
				(AClass) e.nextElement();
			stream.println(" " + c.getBName());
		}
		stream.println(")");

		// print subtypes for builtin types
		for (int i = 0; i < builtinNames.length; ++i) {
			String builtin_name = builtinNames[i];
			stream.println(
				"(FORALL (x) (IFF (<: x (ref "
					+ builtin_name
					+ ")) (EQ x (ref "
					+ builtin_name
					+ "))))");
		}
		stream.println(
			"(FORALL (x y z) (IFF (<: x (array y z)) (EQ x (array y z))))");
		defineSubtypes(config, printer.getClasses());
		defineSubtypes(config, printer.getInterfaces());

		//		// define the supertype of each of the classes, as well as their
		//		// implemented interfaces
		//		e = getClassesAndInterfacesEnumeration();
		//		while (e.hasMoreElements()) {
		//			jml2b.structure.java.Class c =
		//				(jml2b.structure.java.Class) e.nextElement();
		//
		//			// print the superclass
		//			jml2b.structure.java.Class super_class = c.getSuperClass();
		//			if (c != null) {
		//				stream.println(
		//					"(<: (ref "
		//						+ c.getBName()
		//						+ ") (ref "
		//						+ super_class.getBName()
		//						+ "))");
		//			}
		//
		//			// print the superinterfaces
		//			Enumeration imp = c.getImplements();
		//			while (imp.hasMoreElements()) {
		//				Type t = (Type) imp.nextElement();
		//				jml2b.structure.java.Class cl = t.getRefType();
		//
		//				stream.println(
		//					"(<: (ref "
		//						+ c.getBName()
		//						+ ") (ref "
		//						+ cl.getBName()
		//						+ "))");
		//			}
		//		}
		stream.println(")"); // AND
		stream.println(")"); // BG_PUSH

	}

	private void defineSubtypes(IJml2bConfiguration config, AClassEnumeration e) {
		while (e.hasMoreElements()) {
			AClass c = e.nextElement();

			if (c.isObject()) {
				stream.println(
					"(FORALL (x) (<: x (ref " + c.getBName() + ")))");
			} else {
				stream.print(
					"(FORALL (x) (IFF (<: x (ref " + c.getBName() + ")) (OR ");
				defineSubtypesOf(config, printer.getClasses(), new Type(c));
				defineSubtypesOf(config, printer.getInterfaces(), new Type(c));

				if (c.equals("java.lang.Cloneable")
					|| c.equals("java.io.Serializable")) {
					//TODO quid des tableaux pour Simplify
					//stream.println("        | (array _ _) => True");
				}
				stream.println(")))");
			}
		}
	}

	private void defineSubtypesOf(IJml2bConfiguration config, AClassEnumeration e, Type c_type) {
		while (e.hasMoreElements()) {
			AClass subtype = e.nextElement();
			Type s_type = new Type(subtype);

			if (s_type.isSubtypeOf(config, c_type)) {
				stream.println("(EQ x (ref " + subtype.getBName() + "))");
			}
		}
	}

	private void printObjects() {
		stream.println("(DEFPRED (REFERENCES arg1))");
		stream.println("(DEFPRED (instances arg1))");
		stream.println("(BG_PUSH (AND");
		stream.println(
			"(FORALL (x) (EQ (select elemtype (array x 1)) (ref x)))");
		stream.println(
			"(FORALL (x y) (IMPLIES (< 1 y) (EQ (select elemtype (array x y)) (array x (- y 1)))))");
		stream.println(
			"(FORALL (c) (IMPLIES (EQ (|instances| c) |@true|) (REFERENCES c)))"
				+ "(NOT (EQ (|instances| null) |@true|))");
		stream.println("(FORALL (x) (<= 0 (select |arraylength| x)))");
		// properties on the <: operator
		stream.println("(FORALL (x y) (IFF (EQ x y) (EQ (ref x) (ref y))))");
		stream.println("(FORALL (x y z) (NEQ (ref x) (array y z)))");
		stream.println(
			"(FORALL (x y) (<: (select typeof (select (select "
				+ "|refelements| x) y)) (select elemtype (select typeof x))))");
		stream.println(")) ");
		//		stream.println(
		//			"(BG_PUSH (FORALL (c) (<: c c)) "
		//				+ "(FORALL (c1 c2 c3) (IMPLIES (AND (<: c1 c2) (<: c2 c3)) "
		//				+ "(<: c1 c3)))"
		//				+ ")");
	}

	/**
	 * Should push the background predicate corresponding to the
	 * current jpo file.
	 */
	//@ requires simplify != null;
	private void printArithmetics() {
		stream.println("(DEFPRED (BOOL arg1))");
		stream.println("(DEFPRED (t_long arg1))");
		stream.println("(DEFPRED (t_int arg1))");
		stream.println("(DEFPRED (t_short arg1))");
		stream.println("(DEFPRED (t_byte arg1))");
		stream.println("(DEFPRED (t_char arg1))");
		stream
			.println(
				"(BG_PUSH (AND "
				+ "(NOT (EQ |@true| |@false|))\n"
				+ "(FORALL (x) (IFF (BOOL x) (OR (EQ x |@true|) (EQ x |@false|))))\n"
				+ "(FORALL (x) (IFF (t_int x) (AND (<= c_minlong x) (<= x c_maxlong))))\n"
				+ "(FORALL (x) (IFF (t_int x) (AND (<= c_minint x) (<= x c_maxint))))\n"
				+ "(FORALL (x) (IFF (t_short x) (AND (<= c_minshort x) (<= x c_maxshort))))\n"
				+ "(FORALL (x) (IFF (t_byte x) (AND (<= c_minbyte x) (<= x c_maxbyte))))\n"
				+ "(FORALL (x) (IFF (t_char x) (AND (<= c_minchar x) (<= x c_maxchar))))\n"
		// valuates constants corresponding to max and min values
		// as max/min int/long are too large to be used by simplify,
		// they are not valuated, but some basic properties are given 
		// on those constants
		+"(EQ c_minbyte "
			+ (int) Byte.MIN_VALUE
			+ ") "
			+ "(EQ c_maxbyte "
			+ (int) Byte.MAX_VALUE
			+ ") "
			+ "(EQ c_minchar "
			+ (int) Character.MIN_VALUE
			+ ") "
			+ "(EQ c_maxchar "
			+ (int) Character.MAX_VALUE
			+ ") "
			+ "(EQ c_minshort "
			+ (int) Short.MIN_VALUE
			+ ") "
			+ "(EQ c_maxshort "
			+ (int) Short.MAX_VALUE
			+ ")\n"
			+ "(<= c_minint c_minshort) "
			+ "(<= c_maxshort c_maxint) "
			+ "(<= c_minlong c_minint) "
			+ "(<= c_maxint c_maxlong)\n"
			+ 

		// /!\ Warning, the following properties are incorrect properties
		// since overflow could occur
		"(FORALL (a b) (EQ (j_add a b) (+ a b))) "
			+ "(FORALL (a b) (EQ (j_sub a b) (- a b))) "
			+ "(FORALL (a b) (EQ (j_mul a b) (* a b)))\n"
			+ 
		// end of warning

		// properties on cast functions
		"(FORALL (x) (IMPLIES (AND (>= x c_minbyte) (<= x c_maxbyte)) "
			+ "(EQ x (j_int2byte x))))\n"
			+ "(FORALL (x) (IMPLIES (AND (>= x c_minchar) (<= x c_maxchar)) "
			+ "(EQ x (j_int2char x))))\n"
			+ "(FORALL (x) (IMPLIES (AND (>= x c_minshort) (<= x c_maxshort)) "
			+ "(EQ x (j_int2short x))))");

		stream.println(")"); // AND
		stream.println(")"); // BG_PUSH
	}

	void printFieldType(AField f) throws LanguageException {
		if (f.garbage) {
			// ignore fields which do not appear in lemmas
			return;
		}
		// get the type of the field
		Type t = f.getType();

		if (/*t.getTag() == Type.T_FLOAT
																																																																																																																																																																																																																																			||*/
			t.getTag() == Type.T_DOUBLE
				|| t.getTag() == Type.T_LONG
				|| t.getTag() == Type.T_TYPE)
			return;

		if (f.isExpanded())
			return;

		if (firstItem) {
			firstItem = false;
			stream.println("(BG_PUSH (AND");
		}

		if (f.getModifiers().isStatic()) {
			// static field

			if (t.isBuiltin()) {
				stream.println(
					"( "
						+ t.toLang("Simplify").toUniqString()
						+ " "
						+ f.getBName()
						+ ")");
			} else {
				stream.println(
					"(IMPLIES (NEQ "
						+ f.getBName()
						+ " null) (EQ (|instances| "
						+ f.getBName()
						+ ") |@true|))");
				stream.println(
					"(IMPLIES (NEQ "
						+ f.getBName()
						+ " null) (<: (select typeof "
						+ f.getBName()
						+ ") "
						+ t.toLang("Simplify").toUniqString()
						+ "))");
			}
		} else {
			// member field
			if (t.isBuiltin()) {
				stream.println(
					"(FORALL (x) (IMPLIES (instances x) "
						+ "(IMPLIES (<: (select typeof x) "
						+ new SimplifyType(new Type(f.getDefiningClass()))
							.toLang(0)
							.toUniqString()
						+ ") ( "
						+ t.toLang("Simplify").toUniqString()
						+ " (select "
						+ f.getBName()
						+ " x)))))");
			} else {
				stream.println(
					"(FORALL (x) (IMPLIES (EQ (|instances| x) |@true|)"
						+ "(IMPLIES (<: (select typeof x) "
						+ new SimplifyType(new Type(f.getDefiningClass()))
							.toLang(0)
							.toUniqString()
						+ ") (IMPLIES (NEQ (select "
						+ f.getBName()
						+ " x) null) (EQ (|instances| (select "
						+ f.getBName()
						+ " x)) |@true|)))))");
				stream.println(
					"(FORALL (x) (IMPLIES (EQ (|instances| x) |@true|)"
						+ "(IMPLIES (<: (select typeof x) "
						+ new SimplifyType(new Type(f.getDefiningClass()))
							.toLang(0)
							.toUniqString()
						+ ") (IMPLIES (NEQ (select "
						+ f.getBName()
						+ " x) null) (<: (select typeof (select "
						+ f.getBName()
						+ " x)) "
						+ t.toLang("Simplify").toUniqString()
						+ ")))))");
			}
		}

	}

	/**
	 * Prints fields type declaration.
	 * @param e The set of fields
	 **/
	private void printFieldTypes(Enumeration e) throws LanguageException {
		while (e.hasMoreElements()) {
			AField f = (AField) e.nextElement();
			printFieldType(f);
		}
	}

	/**
	 * Prints the fields of a set of classes type declaration.
	 * @param e The set of classes
	 **/
	private void printFieldTypesForClasses(AClassEnumeration e)
		throws LanguageException {
		while (e.hasMoreElements()) {
			AClass c = e.nextElement();
			printFieldTypes(c.getFields());
		}
	}

	/**
	 * Prints the field type declaration
	 **/
	private void printFieldTypes() throws LanguageException {
		firstItem = true;
		printFieldTypesForClasses(printer.getClasses());
		printFieldTypesForClasses(printer.getInterfaces());
	}
	/**
	 * Prints a background predicate suitable for using with the simplify 
	 * prover.
	 */
	public void printBGPredicate(IJml2bConfiguration config) throws LanguageException {
		stream.println("(DEFPRED (<: subtype supertype))");
		printClasses(config);
		printArithmetics();
		printObjects();
		printFieldTypes();
		if (!firstItem) {
			stream.println("))"); // BG_PUSH AND
		}
	}

	/**
	 * Gets an hypothesis corresponding to the AND of all the hypothesis
	 * of the lemma in Simplify's syntax.
	 */
	private String getLemmasHypothesis(Theorem t) throws LanguageException {

		String buf = "(BG_PUSH (AND ";
		Vector formulas = t.getHyp();
		if (formulas.size() == 0) {
			buf += "TRUE";
		} else {
			Enumeration e = formulas.elements();
			while (e.hasMoreElements()) {
				VirtualFormula vf = (VirtualFormula) e.nextElement();
				try {
					SimplifyTranslationResult str =
						(SimplifyTranslationResult) vf.getFormula().toLang(
							"Simplify",
							0);
					String[] st = str.toStrings();
					for (int i = 0; i < st.length; i++)
						buf += st[i];
					buf += str.toUniqString();
				} catch (InternalError ie) {
					buf += ";" + ie.getMessage();
				}
				buf += "\n";
			}
		}

		buf += "))";

		return buf;
	}
	
	private String getPredDecls(Theorem t, Set defpred) throws LanguageException {

		String buf = "";
		Vector formulas = t.getHyp();
		Enumeration e = formulas.elements();
			while (e.hasMoreElements()) {
				VirtualFormula vf = (VirtualFormula) e.nextElement();
				try {
					SimplifyTranslationResult str =
						(SimplifyTranslationResult) vf.getFormula().toLang(
							"Simplify",
							0);
					String[] st = str.getPredDecls();
					for (int i = 0; i < st.length; i++)
						if (!defpred.contains(st[i])) {
								buf += st[i];
								defpred.add(st[i]);
						}
				} catch (InternalError ie) {
					buf += ";" + ie.getMessage();
				}
				buf += "\n";
			}

		return buf;
	}

	private void printGoal(NonObviousGoal g) {
		//stream.println("\n; Goal " g.)
		try {
			SimplifyTranslationResult str =
				(SimplifyTranslationResult) g.getFormula().toLang(
					"Simplify",
					0);
			String[] st = str.toStrings();
			for (int i = 0; i < st.length; i++)
				stream.println("(IMPLIES " + st[i] + " ");
			stream.println(str.toUniqString());
			for (int i = 0; i < st.length; i++)
				stream.println(")");
		} catch (LanguageException le) {
			stream.println(";" + le.getMessage());
		} catch (InternalError e) {
			stream.println(";" + e.getMessage());
		}
	}

	private void printGoals(Enumeration e) {
		if (e.hasMoreElements()) {
			printGoal((NonObviousGoal) e.nextElement());
			printGoals(e);
		}
	}

	private int printProof(IJml2bConfiguration config, Theorem t, SimpleLemma l, int file, Set defpred) {
		stream.println("\n;---Lemma " + t.getName() + "---");
		try {
			stream.println(getPredDecls(t, defpred));
			stream.println(getLemmasHypothesis(t));
			stream.println(";--End of hypothesis--");
			printGoals(l.getGoals());
			stream.println("(BG_POP)");
			if (file / SimplifyPreferencePage.getPoPerFile()
				!= (file + l.nbPo()) / SimplifyPreferencePage.getPoPerFile()) {
				nextFile(config, file / SimplifyPreferencePage.getPoPerFile());
			}
			file += l.nbPo();

		} catch (LanguageException le) {
			stream.println(";" + le.getMessage());
		} catch (InternalError e) {
			stream.println(";" + e.getMessage());
		}
		return file;
	}

	/**
	 * Prints lemmas into the simplify file.
	 * @param lv The lemmas
	 * @param counter The number of goals in the lemmas
	 **/
	private int printProof(IJml2bConfiguration config, Proofs lv, int file, Set defpred) {
		if (lv == null)
			return file;
		for (int i = 0; i < lv.nbLemmas(); i++) {
			Theorem t = lv.getTheorem(i);
			SimpleLemma l = lv.getLemma(i);
			file = printProof(config, t, l, file, defpred);
		}
		return file;
	}
	/**
	 * Prints into the simplify file, the lemmas of a set of methods.
	 * @param e The set of methods
	 **/
	private int printProofMethod(IJml2bConfiguration config, Enumeration e, int file, Set defpred) {
		if (e.hasMoreElements()) {
			Method m =
				(Method) e.nextElement();
			file = printProof(config, m.getLemmas(), file, defpred);
			file = printProof(config, m.getWellDefinednessLemmas(), file, defpred);
			return printProofMethod(config, e, file, defpred);
		} else
			return file;
	}

	/**
	 * Prints into the simplify file, the lemmas of a class.
	 * @param c The class
	 **/
	private int printProof(IJml2bConfiguration config, Class c, int file, Set defpred) {
		file = printProofMethod(config, c.getMethods(), file, defpred);
		file = printProofMethod(config, c.getConstructors(), file, defpred);
		if (c.getStaticInitLemmas() != null)
			file = printProof(config, c.getStaticInitLemmas(), file, defpred);
		return printProof(config, c.getWellDefInvLemmas(), file, defpred);
	}

	/**
	 * Prints into the simplify file, the lemmas of a set of classes.
	 * @param e The set of classes
	 **/
	private void printProof(IJml2bConfiguration config, Enumeration e, int file, Set defpred) {
		if (e.hasMoreElements()) {
			Class c = (Class) e.nextElement();
			file = printProof(config, c, file, defpred);
			printProof(config, e, file, defpred);
		}
	}

	public void printLemmas(IJml2bConfiguration config, JmlFile fi, int file, Set defpred) {
		printProof(config, fi.getClasses(), file, defpred);
	}

	/**
	 * Writes the background predicate file associated with the Simplify prover.
	 * @param printer The file printer
	 * @param fi The current JML file
	 * @param output_directory The folder where the file is to be stored
	 * @throws IOException
	 **/
	public void print(IJml2bConfiguration config, IClassResolver printer, JmlFile fi, File output_directory)
		throws IOException {
		this.printer = printer;
		this.output_directory = output_directory;
		this.fi = fi;

		if (output_directory == null)
			return;

		initFile(config, 0);
		printLemmas(config, fi, 0, new HashSet());
		try {
			ostream.close();
		} catch (IOException e) {
			Logger.err.println("Error closing file: " + ostream.toString());
		}
	}

	void nextFile(IJml2bConfiguration config, int i) {
		try {
			ostream.close();
			initFile(config, i + 1);
		} catch (IOException e) {
			Logger.err.println("Error closing file: " + ostream.toString());
		}
	}

	void initFile(IJml2bConfiguration config, int i) throws IOException {
		File f = getFileName(config, output_directory, fi, i);
		ostream = new BufferedOutputStream(new FileOutputStream(f));
		stream = new PrintStream(ostream);

		// ensure that the file will be closed in case of error
		try {
			printBGPredicate(config);
		} catch (LanguageException le) {
			Logger.err.println(le.getMessage());
		}

	}

	File getFileName(IJml2bConfiguration config, File output_directory, JmlFile fi, int i) {
		String name = fi.getFlatName( config.getPackage());
		name = name + ".sim" + i;
		return new File(output_directory, name);
	}

}

/**
 * Enumeration that allows to iterate over a sequence of enumerations
 */
class SequenceEnumeration implements Enumeration {
	// the enumerations that are used
	private AClassEnumeration[] enumerations;
	private int current;

	public SequenceEnumeration(AClassEnumeration e1, AClassEnumeration e2) {
		enumerations = new AClassEnumeration[2];
		enumerations[0] = e1;
		enumerations[1] = e2;
	}

	public SequenceEnumeration(AClassEnumeration[] e) {
		enumerations = e;
	}

	public boolean hasMoreElements() {
		while (current < enumerations.length) {
			if (enumerations[current].hasMoreElements()) {
				return true;
			}
			++current;
		}

		return false;
	}

	public Object nextElement() {
		if (current >= enumerations.length) {
			throw new NoSuchElementException();
		}

		return enumerations[current].nextElement();
	}
}