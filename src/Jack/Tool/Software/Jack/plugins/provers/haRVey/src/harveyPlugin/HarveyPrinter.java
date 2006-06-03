//******************************************************************************
/* Copyright (c) 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SimplyPrinter
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package harveyPlugin;

import jack.util.Logger;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.Enumeration;
import java.util.NoSuchElementException;
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
public class HarveyPrinter implements IPrinter {

	IClassResolver printer;

	PrintStream stream;

	boolean firstItem;
	IJml2bConfiguration config;
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

	public void printClasses() {

		// define all the classes as distinct elements
		Enumeration e = getClassesAndInterfacesEnumeration();

		while (e.hasMoreElements()) {
			AClass c1 =
				(AClass) e.nextElement();
			Enumeration f = getClassesAndInterfacesEnumeration();
			while (f.hasMoreElements()) {
				AClass c2 =
					(AClass) f.nextElement();
				if (c1 != c2)
					stream.println(
						"(not (= "
							+ c1.getBName()
							+ " "
							+ c2.getBName()
							+ "))");
			}
		}

		// print subtypes for builtin types
		for (int i = 0; i < builtinNames.length; ++i) {
			String builtin_name = builtinNames[i];
			stream.println(
				"(forall x (<-> (subtype x (ref "
					+ builtin_name
					+ ")) (= x (ref "
					+ builtin_name
					+ "))))");
		}

		defineSubtypes(printer.getClasses());
		defineSubtypes(printer.getInterfaces());
	}

	private void defineSubtypes(AClassEnumeration e) {
		while (e.hasMoreElements()) {
			AClass c = e.nextElement();

			if (c.isObject()) {
				stream.println(
					"(forall x (subtype x (ref " + c.getBName() + ")))");
			} else {
				stream.print(
					"(forall x (<-> (subtype x (ref "
						+ c.getBName()
						+ ")) (or ");
				defineSubtypesOf(printer.getClasses(), new Type(c));
				defineSubtypesOf(printer.getInterfaces(), new Type(c));

				if (c.equals("java.lang.Cloneable")
					|| c.equals("java.io.Serializable")) {
					//TODO quid des tableaux pour Harvey
					//stream.println("        | (array _ _) => True");
				}
				stream.println(")))");
			}
		}
	}

	private void defineSubtypesOf(AClassEnumeration e, Type c_type) {
		while (e.hasMoreElements()) {
			AClass subtype = e.nextElement();
			Type s_type = new Type(subtype);

			if (s_type.isSubtypeOf(config, c_type)) {
				stream.println("(= x (ref " + subtype.getBName() + "))");
			}
		}
	}

	private void printObjects() {
		stream.println(
			"(forall c (-> (= (instances c) tt) (REFERENCES c)))"
				+ "(not (= (instances null) tt))");
		stream.println("(forall x y (<-> (= x y) (= (ref x) (ref y))))");
	}

	/**
	 * Should push the background predicate corresponding to the
	 * current jpo file.
	 */
	//@ requires simplify != null;
	private void printArithmetics() {
		stream.println(
			";;; Added by hand since we do not have anything like this built in haRVey");
		stream.println("(not (= tt ff))");

		stream
			.println(
				"(forall x (<-> (pred_BOOL x) (or (= x tt) (= x ff))))\n"
				+ "(forall x (<-> (t_int x) (and (arith_leq c_minlong x) (arith_leq x c_maxlong))))\n"
				+ "(forall x (<-> (t_int x) (and (arith_leq c_minint x) (arith_leq x c_maxint))))\n"
				+ "(forall x (<-> (t_short x) (and (arith_leq c_minshort x) (arith_leq x c_maxshort))))\n"
				+ "(forall x (<-> (t_byte x) (and (arith_leq c_minbyte x) (arith_leq x c_maxbyte))))\n"
				+ "(forall x (<-> (t_char x) (and (arith_leq c_minchar x) (arith_leq x c_maxchar))))\n"
		// valuates constants corresponding to max and min values
		// as max/min int/long are too large to be used by simplify,
		// they are not valuated, but some basic properties are given 
		// on those constants
		//		+"(= c_minbyte "
		//			+ (int) Byte.MIN_VALUE
		//			+ ") "
		//			+ "(= c_maxbyte "
		//			+ (int) Byte.MAX_VALUE
		//			+ ") "
		//			+ "(= c_minchar "
		//			+ (int) Character.MIN_VALUE
		//			+ ") "
		//			+ "(= c_maxchar "
		//			+ (int) Character.MAX_VALUE
		//			+ ") "
		//			+ "(= c_minshort "
		//			+ (int) Short.MIN_VALUE
		//			+ ") "
		//			+ "(= c_maxshort "
		//			+ (int) Short.MAX_VALUE
		//			+ ")\n"
		//			+ "(<= c_minint c_minshort) "
		//			+ "(<= c_maxshort c_maxint) "
		//			+ "(<= c_minlong c_minint) "
		//			+ "(<= c_maxint c_maxlong)\n"
		//			+ 
		//
		//		// /!\ Warning, the following properties are incorrect properties
		//		// since overflow could occur
		//		"(forall a b (= (j_add a b) (+ a b))) "
		//			+ "(forall a b (= (j_sub a b) (- a b))) "
		//			+ "(forall a b (= (j_mul a b) (* a b)))\n" 
		//		// end of warning

		// properties on cast functions
		+"(forall x (-> (and (arith_geq x c_minbyte) (arith_leq x c_maxbyte)) "
			+ "(= x (j_int2byte x))))\n"
			+ "(forall x (-> (and (arith_geq x c_minchar) (arith_leq x c_maxchar)) "
			+ "(= x (j_int2char x))))\n"
			+ "(forall x (-> (and (arith_geq x c_minshort) (arith_leq x c_maxshort)) "
			+ "(= x (j_int2short x))))");

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
		}

		if (f.getModifiers().isStatic()) {
			// static field

			if (t.isBuiltin()) {
				stream.println(
					"( "
						+ t.toLang("Harvey").toUniqString()
						+ " "
						+ f.getBName()
						+ ")");
			} else {
				stream.println(
					"(-> (not (= "
						+ f.getBName()
						+ " null)) (= (instances "
						+ f.getBName()
						+ ") tt))");
				stream.println(
					"(-> (not (= "
						+ f.getBName()
						+ " null)= (subtype (select typeof "
						+ f.getBName()
						+ ") "
						+ t.toLang("Harvey").toUniqString()
						+ "))");
			}
		} else {
			// member field
			if (t.isBuiltin()) {
				stream.println(
					"(forall x (-> (= (instances x) tt)"
						+ "(-> (subtype (select typeof x) "
						+ new HarveyType(new Type(f.getDefiningClass()))
							.toLang(0)
							.toUniqString()
						+ ") ( "
						+ t.toLang("Harvey").toUniqString()
						+ " (select "
						+ f.getBName()
						+ " x)))))");
			} else {
				stream.println(
					"(forall x (-> (= (instances x) tt)"
						+ "(-> (subtype (select typeof x) "
						+ new HarveyType(new Type(f.getDefiningClass()))
							.toLang(0)
							.toUniqString()
						+ ") (-> (not (= (select "
						+ f.getBName()
						+ " x) null)) (= (instances (select "
						+ f.getBName()
						+ " x)) tt)))))");
				stream.println(
					"(forall x (-> (= (instances x) tt)"
						+ "(-> (subtype (select typeof x) "
						+ new HarveyType(new Type(f.getDefiningClass()))
							.toLang(0)
							.toUniqString()
						+ ") (-> (not (= (select "
						+ f.getBName()
						+ " x) null)) (subtype (select typeof (select "
						+ f.getBName()
						+ " x)) "
						+ t.toLang("Harvey").toUniqString()
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
	public void printBGPredicate() throws LanguageException {
		stream.println(";;; Axioms for the theory of arrays...");
		stream.println("(forall A I E (= (select (store A I E) I) E))");
		stream.println(
			"(forall A I J E (-> (not (= I J)) (= (select (store A I E) J) (select A J))))");
		printClasses();
		printArithmetics();
		printObjects();
		printFieldTypes();
	}

	/**
	 * Gets an hypothesis corresponding to the AND of all the hypothesis
	 * of the lemma in Simplify's syntax.
	 */
	private void getLemmasHypothesis(Theorem t) throws LanguageException {

		Vector formulas = t.getHyp();

		Enumeration e = formulas.elements();
		while (e.hasMoreElements()) {
			VirtualFormula vf = (VirtualFormula) e.nextElement();
			try {
				HarveyTranslationResult str =
					(HarveyTranslationResult) vf.getFormula().toLang(
						"Harvey",
						0);
				String[] st = str.toStrings();
				for (int i = 0; i < st.length; i++)
					stream.println(st[i]);
				stream.println(str.toUniqString());
			} catch (InternalError ie) {
				stream.println(";" + ie.getMessage());
			}
		}
	}

	private void printGoal(
		NonObviousGoal g,
		Theorem t,
		File outputDir,
		int numLemma,
		int numGoal)
		throws IOException {
		OutputStream ostream = null;

		try {
			// ensure that the file will be closed in case of error
			File f =
				new File(
					outputDir,
					t.getName() + "_" + numLemma + "_" + numGoal + ".rv");
			ostream = new BufferedOutputStream(new FileOutputStream(f));
			stream = new PrintStream(ostream);
			try {
				stream.println("(");
				printBGPredicate();
				getLemmasHypothesis(t);
				HarveyTranslationResult str =
					(HarveyTranslationResult) g.getFormula().toLang(
						"Harvey",
						0);
				String[] st = str.toStrings();
				for (int i = 0; i < st.length; i++)
					stream.println(st[i]);
				stream.println(")");
				stream.println(";--End of hypothesis--");
				stream.println(str.toUniqString());

			} catch (LanguageException le) {
				stream.println(";" + le.getMessage());
			} catch (InternalError e) {
				stream.println(";" + e.getMessage());
			}
		} finally {
			// close the file after printing (even if an exception is 
			// thrown)
			if (ostream != null) {
				try {
					ostream.close();
				} catch (IOException e) {
					Logger.err.println(
						"Error closing file: " + ostream.toString());
				}
			}
		}
	}

	private void printGoals(
		Enumeration e,
		Theorem t,
		File outputDir,
		int numLemma,
		int numGoal)
		throws IOException {
		if (e.hasMoreElements()) {
			printGoal(
				(NonObviousGoal) e.nextElement(),
				t,
				outputDir,
				numLemma,
				numGoal);
			printGoals(e, t, outputDir, numLemma, ++numGoal);
		}
	}

	private void printProof(
		Theorem t,
		SimpleLemma l,
		File outputDir,
		int numLemma)
		throws IOException {
		printGoals(l.getGoals(), t, outputDir, numLemma, 0);
	}

	//	/**
	//	 * Gets an hypothesis corresponding to the AND of all the hypothesis
	//	 * of the lemma in Simplify's syntax.
	//	 */
	//	private static String getLemmasHypothesis(jpov.structure.Lemma lemma)
	//		throws LanguageException {
	//
	//		StringBuffer buf = new StringBuffer();
	//		buf.append("(AND ");
	//		jpov.structure.VirtualFormula[] formulas = lemma.getHyp();
	//		if (formulas.length == 0) {
	//			buf.append("TRUE");
	//		} else {
	//			for (int i = 0; i < formulas.length; ++i) {
	//				HarveyTranslationResult str =
	//					(HarveyTranslationResult) formulas[i].getF().toLang(
	//						"Simplify",
	//						0);
	//				String[] st = str.toStrings();
	//				for (int j = 0; j < st.length; j++)
	//					buf.append(st[j]);
	//				buf.append(str.toUniqString());
	//				buf.append("\n");
	//			}
	//		}
	//
	//		buf.append(")");
	//
	//		return buf.toString();
	//	}
	//
	//	private void printProof(jpov.structure.Goal g) throws LanguageException {
	//		try {
	//			HarveyTranslationResult str =
	//				(HarveyTranslationResult) g.getFormula().toLang("Simplify", 0);
	//			String[] st = str.toStrings();
	//			for (int i = 0; i < st.length; i++)
	//				stream.println("(IMPLIES " + st[i] + " ");
	//			stream.println(str.toUniqString());
	//			for (int i = 0; i < st.length; i++)
	//				stream.println(")");
	//		} catch (InternalError e) {
	//			stream.println(";" + e.getMessage());
	//		}
	//	}

	//	private void printProof(jpov.structure.Lemma l) throws LanguageException {
	//		stream.println("(BG_PUSH " + getLemmasHypothesis(l) + " )");
	//		for (int i = 0; i < l.getGoals().length; i++)
	//			printProof(l.getGoals()[i]);
	//		stream.println("(BG_POP)");
	//	}

	//	private void printProof(jpov.structure.Proofs p) throws LanguageException {
	//		for (int i = 0; i < p.getLemmasWithPo().length; i++)
	//			printProof(p.getLemmasWithPo()[i]);
	//	}

	/**
	 * Prints lemmas into the simplify file.
	 * @param lv The lemmas
	 * @param counter The number of goals in the lemmas
	 **/
	private void printProof(Proofs lv, File outputDir) throws IOException {
		if (lv == null)
			return;
		for (int i = 0 ; i < lv.nbLemmas(); i++) {
			Theorem t = lv.getTheorem(i);
			SimpleLemma l = lv.getLemma(i);
			printProof(t, l, outputDir, i);
		}
		return;
	}
	/**
	 * Prints into the simplify file, the lemmas of a set of methods.
	 * @param e The set of methods
	 **/
	private void printProofMethod(Enumeration e, File outputDir)
		throws IOException {
		if (e.hasMoreElements()) {
			Method m =
				(Method) e.nextElement();
			printProof(m.getLemmas(), outputDir);
			printProof(m.getWellDefinednessLemmas(), outputDir);
			printProofMethod(e, outputDir);
		}
	}

	//	private void printProof(jpov.structure.Method m) throws LanguageException {
	//		printProof(m.getLemmas());
	//		printProof(m.getWellDefinednessLemmas());
	//	}

	/**
	 * Prints into the simplify file, the lemmas of a class.
	 * @param c The class
	 **/
	private void printProof(jml2b.structure.java.Class c, File outputDir)
		throws IOException {
		printProofMethod(c.getMethods(), outputDir);
		printProofMethod(c.getConstructors(), outputDir);
		if (c.getStaticInitLemmas() != null)
			printProof(c.getStaticInitLemmas(), outputDir);
		printProof(c.getWellDefInvLemmas(), outputDir);
	}

	//	private void printProof(jpov.structure.Class c) throws LanguageException {
	//		for (int i = 0; i < c.getMethods().length; i++)
	//			printProof(c.getMethods()[i]);
	//		for (int i = 0; i < c.getConstructors().length; i++)
	//			printProof(c.getConstructors()[i]);
	//		printProof(c.getStaticInitLemmas());
	//		printProof(c.getWellDefInvLemmas());
	//	}

	/**
	 * Prints into the simplify file, the lemmas of a set of classes.
	 * @param e The set of classes
	 **/
	private void printProof(Enumeration e, File outputDir) throws IOException {
		if (e.hasMoreElements()) {
			Class c =
				(Class) e.nextElement();
			printProof(e, outputDir);
			printProof(c, outputDir);
		}
	}

	public void printLemmas(JmlFile fi, File outputDir)
		throws IOException {
		printProof(fi.getClasses(), outputDir);
	}

	//	public void printLemmas(jpov.structure.JmlFile fi)
	//		throws LanguageException {
	//		for (int i = 0; i < fi.getClasses().length; i++)
	//			printProof(fi.getClasses()[i]);
	//	}

	/**
	 * Writes the background predicate file associated with the harVey prover.
	 * @param printer The file printer
	 * @param fi The current JML file
	 * @param output_directory The folder where the file is to be stored
	 * @throws IOException
	 **/
	public void print(
			IJml2bConfiguration config,
		IClassResolver printer,
		JmlFile fi,
		File output_directory)
		throws IOException {
		this.printer = printer;
		this.config = config;
		if (output_directory != null) {
			File f = new File(output_directory, fi.getFlatName(config.getPackage()) + ".rv");
			f.mkdir();
			output_directory = f;
		} else
			return;

		printLemmas(fi, output_directory);

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