//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
 /* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: CoqPrinter
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/
package pvsPlugin;

import jack.util.Logger;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.Enumeration;
import java.util.HashSet;
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
import jml2b.pog.printers.ClassResolver;
import jml2b.pog.printers.IClassResolver;
import jml2b.pog.printers.IPrinter;
import jml2b.structure.AField;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import jml2b.structure.java.Type;

/**
 * This class provides facilities to write the Coq prelude file
 * 
 * @author L. Burdy
 */
public class PvsPrinter implements IPrinter {

	PrintStream stream;
	IClassResolver printer;

	public PvsPrinter() {
	}

	PvsPrinter(ClassResolver printer, PrintStream stream) {
		this.printer = printer;
		this.stream = stream;
	}

	private String getPredDecls(Theorem t) throws LanguageException {
		HashSet defpred = new HashSet();
		String buf = "";
		Vector formulas = t.getHyp();
		Enumeration e = formulas.elements();
			while (e.hasMoreElements()) {
				VirtualFormula vf = (VirtualFormula) e.nextElement();
				try {
					PvsTranslationResult ctr = (PvsTranslationResult) vf
					.getFormula().toLang("PVS", 0);
					String[] st = ctr.getPredDecls();
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
	private PvsTranslationResult getLemmasHypothesis(Theorem t)
			throws LanguageException {
		PvsTranslationResult res = null;
		Vector formulas = t.getHyp();
		if (formulas.size() != 0) {
			Enumeration e = formulas.elements();
			while (e.hasMoreElements()) {
				VirtualFormula vf = (VirtualFormula) e.nextElement();
				PvsTranslationResult ctr = (PvsTranslationResult) vf
						.getFormula().toLang("PVS", 0);
				if (res == null)
					res = ctr;
				else
					res = new PvsTranslationResult(ctr, res, res.toUniqString()
							+ " =>\n" + ctr.toUniqString());
			}
		}
		return res;
	}

	private int theorem = 0;

	private void printGoal(String theory, PvsTranslationResult ptr, String predDecl,
			NonObviousGoal g, String comment, int goalNum) {
		stream.println(comment + "\n%--- Goal " + goalNum);
		stream.println("T" + theorem + ": THEORY");
		stream.println("BEGIN");
		stream.println("mylib : LIBRARY = \"" + PvsPlugin.getLocation()
				+ "div\"");
		stream.println("IMPORTING mylib@div, mylib@rem");
		stream.println("IMPORTING " + theory);
		try {
			PvsTranslationResult ctr = (PvsTranslationResult) g.getFormula()
					.toLang("PVS", 0);

			String str = (ptr == null || ptr.getLocalDecl() == null ? "" : ptr
					.getLocalDecl());
			str += (ctr.getLocalDecl() == null ? "" : ctr.getLocalDecl());
			stream.println(predDecl + "\n" + str + "\nt" + theorem + ": CONJECTURE");
			if (ptr != null)
				stream.println(ptr.toUniqString() + "=>");
			stream.println(ctr.toUniqString() + "\n");
		} catch (LanguageException le) {
			stream.println("%" + le.getMessage());
		} catch (InternalError e) {
			stream.println("%" + e.getMessage());
		}
		stream.println("END T" + theorem++);
	}

	private void printGoals(String theory, PvsTranslationResult ptr, String predDecl,
			Enumeration e, String comment, int n) {
		if (e.hasMoreElements()) {
			printGoal(theory, ptr, predDecl, (NonObviousGoal) e.nextElement(), comment,
				n++);
			printGoals(theory, ptr, predDecl, e, comment, n);
		}
	}

	private void printProof(String theory, Theorem t, SimpleLemma l, int n) {
		String comment = "\n%--- Method " + t.getName() + "\n%--- Case " + n;
		try {
			printGoals(theory, getLemmasHypothesis(t), getPredDecls(t), l.getGoals(), comment, 1);
		} catch (LanguageException le) {
			stream.println("% " + le.getMessage());
		} catch (InternalError e) {
			stream.println("% " + e.getMessage());
		}
	}

	private void printProof(String theory, Proofs lv) {
		if (lv == null)
			return;
		for (int i = 0; i < lv.nbLemmas(); i++) {
			Theorem t = lv.getTheorem(i);
			SimpleLemma l = lv.getLemma(i);
			printProof(theory, t, l, i + 1);
		}
		return;
	}

	private void printProofMethod(String theory, Enumeration e) {
		if (e.hasMoreElements()) {
			Method m = (Method) e.nextElement();
			printProof(theory, m.getLemmas());
			printProof(theory, m.getWellDefinednessLemmas());
			printProofMethod(theory, e);
		}
	}

	private void printProof(String theory, jml2b.structure.java.Class c) {
		printProofMethod(theory, c.getMethods());
		printProofMethod(theory, c.getConstructors());
		if (c.getStaticInitLemmas() != null)
			printProof(theory, c.getStaticInitLemmas());
		printProof(theory, c.getWellDefInvLemmas());
	}

	private void printProof(String theory, Enumeration e) {
		if (e.hasMoreElements()) {
			Class c = (Class) e.nextElement();
			printProof(theory, c);
			printProof(theory, e);
		}
	}

	private void printLemmas(IJml2bConfiguration config, JmlFile fi) {
		theorem = 0;
		printProof(fi.getFlatName(config.getPackage()) + "_prelude", fi.getClasses());
	}

	//	/**
	//	  * Prints the prelude in a vernacular file
	//	  * @param config The current configuration
	//	  **/
	private void printPvs(IJml2bConfiguration config, JmlFile fi) throws LanguageException {
		stream.println(fi.getFlatName(config.getPackage()) + "_prelude : THEORY\n");
		stream.println("BEGIN\n");
		stream.println("mylib : LIBRARY = \"" + PvsPlugin.getLocation()
				+ "div\"");
		stream.println("IMPORTING mylib@div, mylib@rem");
		printPrelude(config);
		stream.println("END " + fi.getFlatName(config.getPackage()) + "_prelude\n");
		//		printLemmas(fi);
	}

	/**
	 * Prints the inductive definition of the set representing the classes
	 */
	private void defineClasses() {
		stream.println("\nClasses : TYPE = {");

		// print builtin types
		for (int i = 0; i < builtinNames.length; ++i) {
			if (i != 0)
				stream.print(",\n");
			stream.print("   " + builtinNames[i]);
		}

		// print classes
		defineClasses(printer.getClasses());
		defineClasses(printer.getInterfaces());
		stream.println("}\n\n");
	}

	/**
	 * Prints the classes as member of the inductive classes set
	 * 
	 * @param e
	 *            The set of classes
	 */
	private void defineClasses(AClassEnumeration e) {
		while (e.hasMoreElements()) {
			AClass c = e.nextElement();
			stream.print(",\n");
			stream.print("   " + c.getBName());
		}
	}

	/**
	 * Prints the arithmetic operators definition
	 */
	private void defineArithmetics() {
		stream.println("c_minint : integer = -2147483648");
		stream.println("c_maxint : integer = 2147483647");
		stream.println("c_maxshort : integer = 32767");
		stream.println("c_minshort : integer = -32768");
		stream.println("c_maxbyte : integer = 127");
		stream.println("c_minbyte : integer = -128");
		stream.println("c_minchar : integer = 0");
		stream.println("c_maxchar : integer = 65535\n");
		stream
				.println("t_int : TYPE = {x: integer | c_minint <= x AND x <= c_maxint} CONTAINING 0");
		stream
				.println("t_short : TYPE = {x: integer | c_minshort <= x AND x <= c_maxshort} CONTAINING 0");
		stream
				.println("t_byte : TYPE = {x: integer | c_minbyte <= x AND x <= c_maxbyte} CONTAINING 0");
		stream
				.println("t_char : TYPE = {x: integer | c_minchar <= x AND x <= c_maxchar} CONTAINING 0");

		stream
				.println("j_add : [integer, integer -> integer] = (LAMBDA (x,y:integer): x + y)");

		stream
				.println("j_sub : [integer, integer -> integer] = (LAMBDA (x,y:integer): x - y)");

		stream
				.println("j_mul : [integer, integer -> integer] = (LAMBDA (x,y:integer): x * y)");

		stream
				.println("j_div : [integer, nonzero_integer -> integer] = (LAMBDA (x:integer,y:nonzero_integer): div(x,y))");

		stream
				.println("j_rem : [integer, nonzero_integer -> integer] = (LAMBDA (x:integer,y:nonzero_integer): rem(x,y))");

		stream
				.println("j_neg : [integer -> integer] = (LAMBDA (x:integer): -x)");
		stream.println("j_shl : [integer, integer -> integer]");
		stream.println("j_shr : [integer, integer -> integer]");
		stream.println("j_ushr : [integer, integer -> integer]");
		stream.println("j_and : [integer, integer -> integer]");
		stream.println("j_or : [integer, integer -> integer]");
		stream.println("j_xor : [integer, integer -> integer]\n");

		stream.println("j_int2char : [t_int -> t_char]");
		stream
				.println("j_int2charId : AXIOM (FORALL (n:t_char): j_int2char(n) = n)\n");

		stream.println("j_int2byte : [t_int -> t_byte]");
		stream
				.println("j_int2byteId : AXIOM (FORALL (n:t_byte): j_int2byte(n) = n)\n");

		stream.println("j_int2short : [t_int -> t_short]");
		stream
				.println("j_int2shortId : AXIOM (FORALL (n:t_int): j_int2short(n) = n)\n");

		//		stream.println("Axiom j_int2byteAx : ");
		//		stream.println(" (n:Z) (t_int n) ");
		//		stream.println(" -> ((Zle `0` n)");
		//		stream.println(" -> ((Zle (Zmod n `256`) `127`)");
		//		stream.println(
		//			" -> (eq Z (j_int2byte n) (Zmod n `256`))");
		//		stream.println(" /\\ (not (Zle (Zmod n `256`) `127`))");
		//		stream.println(
		//			" -> "
		//				+ "(eq Z (j_int2byte n) (Zminus (Zmod n `256`) `256`))");
		//		stream.println(" /\\ (not (Zle `0` n))");
		//		stream.println(
		//			" -> "
		//				+ "(eq Z (j_int2byte n) "
		//				+ "(j_int2byte "
		//				+ "(Zplus n (Zmult (Zplus (Zdiv `-n` `256`) `1`) `256`)))))).");
	}

	/**
	 * Prints the memory model variable definitions
	 */
	private void defineObjects() {
		stream.println("Types : DATATYPE");
		stream.println("    BEGIN");
		stream.println("      class (c: Classes) : class?");
		stream.println("      arrays (c: Classes, n : posnat) : arrays?");
		stream.println("    END Types\n");

		stream.println("REFERENCES : DATATYPE");
		stream.println("    BEGIN");
		stream.println("      null : null?");
		stream.println("      instances (typeof : Types) : instances?");
		stream.println("    END REFERENCES\n");

		stream.println("STRING : NONEMPTY_TYPE");
		stream.println("j_string : [STRING -> REFERENCES]\n");
	}

	private static String defineArray(String t) {
		return "[y:{x : REFERENCES | instances?(x) AND typeof(x) = arrays(c_"
				+ t + ",1)} -> [below(arraylength(y)) -> t_" + t + "]]";
	}

	static String arrayType(int tag) {
		switch (tag) {
			case Type.T_BOOLEAN :
				return "[y:{x : REFERENCES | instances?(x) "
						+ "AND typeof(x) = arrays(c_boolean, 1)} "
						+ "-> [below(arraylength(y)) -> bool]]";
			case Type.T_BYTE :
				return defineArray("byte");
			case Type.T_CHAR :
				return defineArray("char");
			case Type.T_SHORT :
				return defineArray("short");
			case Type.T_INT :
				return defineArray("int");
			default :
				return "[y:{x:REFERENCES | instances?(x) AND arrays?(typeof(x))"
						+ " AND typeof(x) /= arrays(c_boolean,1)"
						+ " AND typeof(x) /= arrays(c_byte,1)"
						+ " AND typeof(x) /= arrays(c_char,1)"
						+ " AND typeof(x) /= arrays(c_short,1)"
						+ " AND typeof(x) /= arrays(c_int,1)"
						+ "} -> [below(arraylength(y)) -> REFERENCES]]";

		}
	}

	/**
	 * Prints the variables corresponding to arrays.
	 */
	private void defineArrays() {
		stream.println("elemtype : [{t:Types | arrays?(t)} -> Types] =");
		stream
				.println("   (LAMBDA (t:{t:Types | arrays?(t)}): CASES t OF\n"
						+ "      arrays(c,n) : IF n > 1 THEN arrays(c, n-1) ELSE class(c) ENDIF\n"
						+ "     ENDCASES)\n");

		stream
				.println("arraylength : [{x:REFERENCES | instances?(x) AND arrays?(typeof(x))} -> nat]");

		stream.println("intelements : " + arrayType(Type.T_INT));
		stream.println("shortelements : " + arrayType(Type.T_SHORT));
		stream.println("charelements : " + arrayType(Type.T_CHAR));
		stream.println("byteelements : " + arrayType(Type.T_BYTE));
		stream.println("booleanelements : " + arrayType(Type.T_BOOLEAN));

		stream.println("refelements : " + arrayType(Type.T_REF) + "\n");
	}

	/**
	 * Prints the subtypes definition and the field declaration.
	 * 
	 * @param config
	 *            The current configuration
	 */
	private void defineLocal(IJml2bConfiguration config) throws LanguageException {
		stream.println("subtype : [Types ,Types -> bool] =");
		stream.println("   (LAMBDA (t1,t2:Types):");
		stream.println("      CASES t2 OF");
		stream.println("         class(c) :");
		stream.println("            CASES c OF");
		defineSubtypes(config);
		stream.println("");
		stream.println("            ENDCASES,\n");
		stream.println("         arrays(s,t) : t1 = t2");
		stream.println("      ENDCASES)\n");
		printFieldTypes();
	}

	/**
	 * Prints the subtypes valuation
	 * 
	 * @param config
	 *            The current configuration
	 */
	private void defineSubtypes(IJml2bConfiguration config) {
		// print subtypes for builtin types
		for (int i = 0; i < builtinNames.length; ++i) {
			String builtin_name = builtinNames[i];
			if (i != 0)
				stream.println(",\n\n");
			stream.print("            " + builtin_name + " : t1 = t2");
		}

		defineSubtypes(config, printer.getClasses());
		defineSubtypes(config, printer.getInterfaces());
	}

	/**
	 * Prints the subtypes valuation for a set of classes
	 * 
	 * @param config
	 *            The current configuration
	 * @param e
	 *            The set of classes
	 */
	private void defineSubtypes(IJml2bConfiguration config, AClassEnumeration e) {
		while (e.hasMoreElements()) {
			AClass c = e.nextElement();

			if (c.isObject()) {
				stream.print(",\n\n            " + c.getBName() + " : true");
			} else {
				stream.println(",\n\n            " + c.getBName()
						+ " : CASES t1 OF");
				stream.println("               class(c1): CASES c1 OF");
				boolean first1 = defineSubtypesOf(config, printer.getClasses(), c, true);
				defineSubtypesOf(config, printer.getInterfaces(), c, first1);
				stream.println("\n                  ELSE false");
				stream.print("               ENDCASES");

				if (c.equals("java.lang.Cloneable")
						|| c.equals("java.io.Serializable")) {
					if (!first1)
						stream.println(",");
					stream.print("               arrays(x,y) : true");
					//TODO V?rifier la correction de arrays(x,y)
				} else
					stream.println("\n               ELSE false");
				stream.print("            ENDCASES");
			}
		}
	}

	/**
	 * Prints the subtypes valuation for a class
	 * 
	 * @param config
	 *            The current configuration
	 * @param e
	 *            The current set of classes
	 * @param c
	 *            The class
	 */
	private boolean defineSubtypesOf(IJml2bConfiguration config, AClassEnumeration e, AClass c, boolean first) {
		Type c_type = new Type(c);

		while (e.hasMoreElements()) {
			AClass subtype = e.nextElement();
			Type s_type = new Type(subtype);

			if (s_type.isSubtypeOf(config, c_type)) {
				if (first)
					first = false;
				else
					stream.println(",");
				stream.print("                  " + subtype.getBName()
						+ ": true");
			}
		}
		return first;
	}

	/**
	 * Prints a field declaration
	 * 
	 * @param f
	 *            The field
	 */
	void printFieldType(AField f) {
		if (f.garbage) {
			// ignore fields which do not appear in lemmas
			return;
		}

		if (f.isExpanded())
			return;

		// get the type of the field
		Type t = f.getType();

		if (t.getTag() == Type.T_DOUBLE || t.getTag() == Type.T_LONG)
			return;

		if (f.getModifiers().isStatic())
			// static field
			stream.println(f.getBName() + " : " + getPvsType(t));
		else
			// member field
			stream.println(f.getBName() + " : ["
					+ getPvsType(new Type(f.getDefiningClass())) + " -> "
					+ getPvsType(t) + "]");

	}

	/**
	 * Prints fields type declaration.
	 * 
	 * @param e
	 *            The set of fields
	 */
	private void printFieldTypes(Enumeration e) throws LanguageException {
		while (e.hasMoreElements()) {
			AField f = (AField) e.nextElement();
			printFieldType(f);
		}
	}

	/**
	 * Prints the fields of a set of classes type declaration.
	 * 
	 * @param e
	 *            The set of classes
	 */
	private void printFieldTypesForClasses(AClassEnumeration e)
			throws LanguageException {
		while (e.hasMoreElements()) {
			AClass c = e.nextElement();
			printFieldTypes(c.getFields());
		}
	}

	/**
	 * Prints the field type declaration
	 */
	private void printFieldTypes() throws LanguageException {
		//firstItem = true;
		printFieldTypesForClasses(printer.getClasses());
		printFieldTypesForClasses(printer.getInterfaces());
	}

	/**
	 * Returns the super type of a type
	 * 
	 * @param tag
	 *            The tag associated to a type
	 * @return The Cop type
	 */
	static public String getPvsType(Type t) {
		switch (t.getTag()) {
			case Type.T_LONG :
				return "t_long";
			case Type.T_FLOAT :
				return "t_float";
			case Type.T_INT :
				return "t_int";
			case Type.T_SHORT :
				return "t_short";
			case Type.T_CHAR :
				return "t_char";
			case Type.T_BYTE :
				return "t_byte";
			case Type.T_BOOLEAN :
				return "bool";
			case Type.T_REF :
				return "{ x : REFERENCES | instances?(x) AND subtype(typeof(x), class("
						+ t.getRefType().getBName() + "))}";
			case Type.T_ARRAY :
				return "{ x : REFERENCES | instances?(x) AND subtype(typeof(x), arrays("
						+ getArrayClass(t) + "," + t.getDimension() + "))}";
			case Type.T_TYPE :
				return "Types";
			default :
				throw new InternalError("Unhandled case in "
						+ "PvsPrinter.getPvsType(Type):" + t.getTag());
		}
	}

	/**
	 * Returns the class of the element of an array
	 * 
	 * @param t
	 *            The arary type
	 */
	static private String getArrayClass(Type t) {
		switch (t.getTag()) {
			case Type.T_INT :
				return "c_int";
			case Type.T_SHORT :
				return "c_short";
			case Type.T_CHAR :
				return "c_char";
			case Type.T_BYTE :
				return "c_byte";
			case Type.T_BOOLEAN :
				return "c_bool";
			case Type.T_LONG :
				return "c_long";
			case Type.T_FLOAT :
				return "c_float";
			case Type.T_DOUBLE :
				return "c_double";
			case Type.T_REF :
				return t.getRefType().getBName();
			case Type.T_ARRAY :
				return getArrayClass(t.getElemType());
			default :
				throw new InternalError("Unhandled case in "
						+ "PvsPrinter.getArrayClass(Type)");
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see jml2b.pog.printers.IPrinter#print(jml2b.IJml2bConfiguration,
	 *      org.eclipse.core.runtime.IProgressMonitor,
	 *      jml2b.pog.printers.Printer, jml2b.structure.java.JmlFile,
	 *      java.io.File)
	 */
	public void print(IJml2bConfiguration config, IClassResolver printer, JmlFile fi, File output_directory)
			throws IOException {

		this.printer = printer;
		OutputStream ostream = null;

		if (output_directory != null) {
			File f = new File(output_directory, fi.getFlatName(config.getPackage())
					+ "_prelude.pvs");
			ostream = new BufferedOutputStream(new FileOutputStream(f));
			stream = new PrintStream(ostream);
		} else {
			// if no output directory is given, print to stream
			stream = Logger.out;
		}
		// ensure that the file will be closed in case of error
		try {
			printPvs(config, fi);
		} catch (LanguageException le) {
			Logger.err.println(le.getMessage());
		} finally {
			// close the file after printing (even if an exception is
			// thrown)
			if (ostream != null) {
				try {
					ostream.close();
				} catch (IOException e) {
					Logger.err.println("Error closing file: "
							+ ostream.toString());
				}
			}
		}
		if (output_directory != null) {
			File f = new File(output_directory, fi.getFlatName(config.getPackage()) + ".pvs");
			ostream = new BufferedOutputStream(new FileOutputStream(f));
			stream = new PrintStream(ostream);
		} else {
			// if no output directory is given, print to stream
			stream = Logger.out;
		}
		printLemmas(config, fi);
		// close the file after printing
		if (ostream != null) {
			try {
				ostream.close();
			} catch (IOException e) {
				Logger.err.println("Error closing file: " + ostream.toString());
			}
		}

	}

	void printPrelude(IJml2bConfiguration config) throws LanguageException {
		defineClasses();
		defineArithmetics();
		defineObjects();
		defineArrays();
		defineLocal(config);
	}
}