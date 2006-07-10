//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
 /* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: BPrinter.java
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /*  09/26/2003 : Simplify integration achieved
 /******************************************************************************/

package bPlugin;

import jack.util.Logger;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.LanguageException;
import jml2b.formula.Formula;
import jml2b.pog.lemma.NonObviousGoal;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.printers.AClassEnumeration;
import jml2b.pog.printers.IClassResolver;
import jml2b.pog.printers.IPrinter;
import jml2b.structure.IClass;
import jml2b.structure.java.AClass;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;

/**
 * @author lburdy
 * 
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class BPrinter implements IPrinter {

	/**
	 * name of the set representing classes
	 */
	public static final String NAMES = "NAMES";

	/**
	 * This string corresponds to the set of all the types, it is defined when
	 * the number of classes in the enumerate is known.
	 * <code>"(1.." + cpt + ")*{" + NAMES + "}*NATURAL"</code>
	 */
	static String defTYPES;

	/**
	 * The string corresponding to the int builtin type, as a member of the
	 * NAMES enumeration.
	 */
	public static String c_int = "1 |-> " + NAMES;

	/**
	 * The string corresponding to the short builtin type, as a member of the
	 * NAMES enumeration.
	 */
	public static String c_short = "2 |-> " + NAMES;

	/**
	 * The string corresponding to the char builtin type, as a member of the
	 * NAMES enumeration.
	 */
	public static String c_char = "3 |-> " + NAMES;

	/**
	 * The string corresponding to the boolean builtin type, as a member of the
	 * NAMES enumeration.
	 */
	public static String c_boolean = "5 |-> " + NAMES;

	/**
	 * The string corresponding to the byte builtin type, as a member of the
	 * NAMES enumeration.
	 */
	public static String c_byte = "4 |-> " + NAMES;

	/**
	 * The string corresponding to the set of all array types
	 */
	static String defARRAYS;

	/**
	 * The string corresponding to the set of all builtin types
	 */
	static String defBUILTIN_NAMES = "{" + c_int + "," + c_short + "," + c_char + "," + c_byte + "," + c_boolean + "}";

	/**
	 * The array of strings corresponding to builtin types
	 */
	static String[] builtinDefNames = {c_int, c_short, c_char, c_byte, c_boolean};

	/**
	 * The string corresponding to the types enumerate
	 */
	static String defNAMES;

	/**
	 * Writes a class with the B Syntax.
	 * 
	 * @param c
	 *                    The displayed class
	 * @return the string corresponding to the element of the class enumeration
	 *                with 0 as dimension
	 */
	String getBClass(BClass c) {
		if (c.enumerationRank == 0)
			Logger.warn.println("enumeration rank == 0");
		return c.enumerationRank + "|->" + NAMES + " |-> 0";
	}

	static BClass getBClass(IClass a) throws LanguageException {
		if (bClasses == null)
			throw new LanguageException("B outputfile has not been generated");
		Enumeration e = bClasses.elements();
		while (e.hasMoreElements()) {
			BClass bc = (BClass) e.nextElement();
			if (bc.getAc().getBName().equals(a.getBName()))
				return bc;
		}
		e = bInterfaces.elements();
		while (e.hasMoreElements()) {
			BClass bc = (BClass) e.nextElement();
			if (bc.getAc().getBName().equals(a.getBName()))
				return bc;
		}
		return null;
	}

	/**
	 * Utility boolean used to write list into the file
	 */
	boolean firstItem;

	PrintStream stream;
	IClassResolver printer;

	private static Vector bClasses;
	private static Vector bInterfaces;

	/**
	 * The hash table associating an index to a formula
	 */
	Hashtable formulaRank;

	//	BPrinter(Printer fp, PrintStream ps) {
	//		printer = fp;
	//		stream = ps;
	//	}
	//
	//	BPrinter(PrintStream ps) {
	//		stream = ps;
	//	}

	/**
	 * Prints all the hypothesis and all the goals of a proof. Associated an
	 * index to each hypothese.
	 * 
	 * @param p
	 *                    The proof
	 * @param cpt
	 *                    The current hypothese counter
	 * @return The current updated hypothese counter
	 */
	int printFormulas(Proofs p, int cpt) {
		try {
			if (p != null/* && p.getThl() != null */) {
				Enumeration e = p.getLocHyp();
				while (e.hasMoreElements()) {
					VirtualFormula vf = (VirtualFormula) e.nextElement();
					if (p.isUsed(vf) && vf.getOrigin() != VirtualFormula.STATIC_FINAL_FIELDS_INVARIANT) {
						Formula f = vf.getFormula();
						formulaRank.put(f, new Integer(cpt++));
						stream.print(";\n(" + f.toLang("B", 0).toUniqString() + ")");
					}
				}
				for (int i = 0; i < p.nbLemmas(); i++) {
					SimpleLemma l = p.getLemma(i);
					Enumeration e1 = l.getGoals();
					while (e1.hasMoreElements()) {
						NonObviousGoal g = (NonObviousGoal) e1.nextElement();
						formulaRank.put(g.getFormula(), new Integer(cpt++));
						stream.print(";\n(" + g.getFormula().toLang("B", 0).toUniqString() + ")");
					}
				}
			}
		} catch (LanguageException le) {
			;
		}

		return cpt;
	}

	/**
	 * Print the part of the valuation of the <code>subtypes</code> relation
	 * corresponding to a class.
	 * 
	 * @param config
	 *                    The current configuration
	 * @param e
	 *                    The set of classes
	 * @param c
	 *                    The class
	 * @param is_first
	 *                    indicates whether the valuation has begun or not
	 * @return whether the valuation has begun or not
	 */
	private boolean printSubtypesOf(IJml2bConfiguration config, Enumeration e, BClass c, boolean is_first) {
		Type c_type = new Type(c.getAc());

		while (e.hasMoreElements()) {
			BClass subtype = (BClass) e.nextElement();
			Type s_type = new Type(subtype.getAc());

			if (s_type.isSubtypeOf(config, c_type)) {
				if (is_first) {
					is_first = false;
				} else {
					stream.print("} \\/ {");
				}
				try {
					stream.println(s_type.toLang("B").toUniqString());
				} catch (LanguageException le) {
					;
				}

			}
		}
		return is_first;
	}

	/**
	 * Print the part of the valuation of the <code>subtypes</code> relation
	 * corresponding to a set of classes.
	 * 
	 * @param config
	 *                    The current configuration
	 * @param e
	 *                    The set of classes
	 */
	private void printSubtypes(IJml2bConfiguration config, Enumeration e) {
		while (e.hasMoreElements()) {
			BClass c = (BClass) e.nextElement();
			stream.print(" & subtypes[{" + getBClass(c) + "}] = ");

			if (c.getAc().isObject()) {
				stream.println(defTYPES + " - " + defBUILTIN_NAMES + " * {0}");
			} else {
				stream.print("{");
				boolean is_first = printSubtypesOf(config, getClasses(), c, true);
				printSubtypesOf(config, getInterfaces(), c, is_first);

				stream.print("}");

				if (c.equals("java.lang.Cloneable") || c.equals("java.io.Serializable")) {
					stream.println(" \\/ " + defARRAYS);
				} else
					stream.println("");
			}
		}
	}

	/**
	 * Print the valuation of the <code>subtypes</code> relation
	 * 
	 * @param config
	 *                    The current configuration
	 */
	void printSubtypes(IJml2bConfiguration config) {
		// print subtypes for builtin types
		int count = builtinDefNames.length;
		for (int i = 0; i < count; ++i) {
			String builtin_name = builtinDefNames[i];
			stream.println(" & " + "subtypes[{" + builtin_name + " |-> 0 }] = { " + builtin_name + " |-> 0 }");
		}

		printSubtypes(config, getClasses());
		printSubtypes(config, getInterfaces());
	}

	/**
	 * Returns the B declaration corresponding to a type.
	 * 
	 * @param t
	 *                    The type
	 * @return The B type if the type is builtin, the set of corresponding
	 *                instances if the type is a ref or a refarray
	 */
	static String getBType(Type t) {
		try {
			switch (t.getTag()) {
				case Type.T_INT :
				case Type.T_BYTE :
				case Type.T_BOOLEAN :
				case Type.T_SHORT :
				case Type.T_CHAR :
				case Type.T_FLOAT :
				case Type.T_LONG :
				case Type.T_DOUBLE :
					return t.toLang("B").toUniqString();
				case Type.T_TYPE :
					return BPrinter.TYPES;
				case Type.T_REF :
				case Type.T_ARRAY :
					return "typeof~[subtypes[{ " + t.toLang("B").toUniqString() + "}]] \\/ { null }";
			}
		} catch (LanguageException le) {
			;
		}
		throw new jml2b.exceptions.InternalError("FilePrinter.getBType Unknown type " + t.getTag());
	}

	/**
	 * name of the set representing types
	 */
	public static final String TYPES = "TYPES";

	/**
	 * Writes the po file associated with Atelier B.
	 * 
	 * @param config
	 *                    The current configuration
	 * @param printer
	 *                    The file printer
	 * @param fi
	 *                    The current JML file
	 * @param output_directory
	 *                    The folder where the file is to be stored
	 * @throws IOException
	 */
	private void printPo(IJml2bConfiguration config, JmlFile fi, File output_directory) throws IOException {

		OutputStream ostream = null;

		if (output_directory != null) {
			File f = new File(output_directory, fi.getFlatName(config.getPackage()) + ".po");
			ostream = new BufferedOutputStream(new FileOutputStream(f));
			stream = new PrintStream(ostream);
		} else {
			// if no output directory is given, print to stream
			stream = Logger.out;
		}
		// ensure that the file will be closed in case of error
		try {
			PoPrinter poprinter = new PoPrinter(this, stream);
			poprinter.printTheoryEnumerateX();
			poprinter.printTheoryFormulas(config, fi);
			poprinter.printTheoryProofList(fi);
		} catch (LanguageException le) {
			Logger.err.println(le.getMessage());
		} finally {
			// close the file after printing (even if an exception is
			// thrown)
			if (ostream != null) {
				try {
					ostream.close();
				} catch (IOException e) {
					Logger.err.println("Error closing file: " + ostream.toString());
				}
			}
		}

	}

	/**
	 * Writes the file containing a machine associated with Atelier B.
	 * 
	 * @param config
	 *                    The current configuration
	 * @param printer
	 *                    The file printer
	 * @param fi
	 *                    The current JML file
	 * @param output_directory
	 *                    The folder where the file is to be stored
	 * @throws IOException
	 */
	private void printMch(IJml2bConfiguration config, IClassResolver printer, JmlFile fi, File output_directory) throws IOException {

		OutputStream ostream = null;

		if (output_directory != null) {
			File f = new File(output_directory, fi.getFlatName(config.getPackage()) + ".mch");
			ostream = new BufferedOutputStream(new FileOutputStream(f));
			stream = new PrintStream(ostream);
		} else {
			// if no output directory is given, print to stream
			stream = Logger.out;
		}
		// ensure that the file will be closed in case of error
		try {
			MchPrinter mchPrinter = new MchPrinter(this, stream);
			mchPrinter.printMchHeader(config, fi);
			mchPrinter.printConstants(config);
			mchPrinter.printProperties(config, fi);
			mchPrinter.printAssertions(fi);
		} catch (LanguageException le) {
			Logger.err.println(le.getMessage());
		} finally {
			// close the file after printing (even if an exception is
			// thrown)
			if (ostream != null) {
				try {
					ostream.close();
				} catch (IOException e) {
					Logger.err.println("Error closing file: " + ostream.toString());
				}
			}
		}

	}

	public void print(IJml2bConfiguration config, IClassResolver printer, JmlFile file, File output_directory) throws IOException {
		this.printer = printer;
		formulaRank = new Hashtable();
		printPo(config, file, output_directory);

		//		printPmi(file, output_directory);

		printMch(config, printer, file, output_directory);
	}

	/**
	 * Prints a set of classes and assocates to each one an enumeration rank.
	 * 
	 * @param e
	 *                    The set of classes
	 * @param cpt
	 *                    The current enumeration rank
	 * @return The updated enumeration rank
	 */
	int printClasses(Enumeration e, int cpt) {
		while (e.hasMoreElements()) {
			BClass c = (BClass) e.nextElement();
			c.enumerationRank = cpt++;
			stream.print(",");
			stream.println(c.getAc().getBName());
		}
		return cpt;
	}

	/**
	 * Prints the part of the prelude concerning the properties of
	 * <code>null, subtypes, instances, typeof, j_string, elemtype, 
	 * arraylength, xxxelements </code>.
	 * 
	 * @param mch
	 *                    Indicates whether formulas should be normalized or not
	 */
	void printJml2bDefs(IJml2bConfiguration config,boolean mch) {
		stream.println("null: REFERENCES & ");
		stream.println("subtypes: " + defTYPES + " <-> " + defTYPES + " & ");
		stream.println("instances: POW(REFERENCES) & ");
		stream.println("not(null: instances) & ");
		stream.println("typeof: instances +-> " + defTYPES + " & ");
		stream.println("dom(typeof) = instances & ");

		IClass string = config.getPackage().getJavaLangString();
		if (string != null) {
			try {
				BClass bclss = getBClass(string);
				if (bclss != null)
					stream.println("j_string : STRING +-> typeof~[{" + getBClass(getBClass(string)) + "}] &");
			}
			catch (LanguageException le) {}
			stream.println("dom(j_string) = STRING &");
		}

		stream.println("elemtype: " + defARRAYS + " +-> " + defTYPES + " & ");
		stream.println("dom(elemtype) = " + defARRAYS + " & ");
		stream.println("arraylength: typeof~[" + defARRAYS + "] +-> NATURAL & ");
		stream.println("dom(arraylength) = typeof~[" + defARRAYS + "] & ");

		stream.println("intelements: " + arrayDecl(Type.T_INT) + " &");
		stream.println("dom(intelements) = typeof~[{" + c_int + "|->1}] & ");
		stream.println("!array.(array: dom(intelements) => " + "dom(intelements(array)) = 0..arraylength(array)-1) & ");

		stream.println("charelements:" + arrayDecl(Type.T_CHAR) + " &");
		stream.println("dom(charelements) = typeof~[{" + c_char + "|->1}] & ");
		stream.println("!array.(array: dom(charelements) => "
						+ "dom(charelements(array)) = 0..arraylength(array)-1) & ");
		stream.println("shortelements:" + arrayDecl(Type.T_SHORT) + " &");
		stream.println("dom(shortelements) = typeof~[{" + c_short + "|->1}] & ");
		stream.println("!array.(array: dom(shortelements) => "
						+ "dom(shortelements(array)) = 0..arraylength(array)-1) & ");

		stream.println("byteelements: " + arrayDecl(Type.T_BYTE) + " &");
		stream.println("dom(byteelements) = typeof~[{" + c_byte + "|->1}] & ");
		stream.println("!array.(array: dom(byteelements) => "
						+ "dom(byteelements(array)) = 0..arraylength(array)-1) & ");

		stream.println("booleanelements: " + arrayDecl(Type.T_BOOLEAN) + " &");
		stream.println("dom(booleanelements) = typeof~[{" + c_boolean + "|->1}] & ");
		stream.println("!array.(array: dom(booleanelements) => "
						+ "dom(booleanelements(array)) = 0..arraylength(array)-1) & ");

		stream.println("refelements: " + arrayRefDecl("instances\\/{null}") + " &");
		stream.println("dom(refelements) = typeof~[" + defARRAYS + "-({" + c_int + "}\\/{" + c_char + "}\\/{" + c_short
						+ "}\\/{" + c_byte + "}\\/{" + c_boolean + "})*{1}] & ");
		stream.println("!array.(array: dom(refelements) => " + "dom(refelements(array)) = 0..arraylength(array)-1 & ");
		stream.println("ran(refelements(array)): " + "POW(typeof~[subtypes[{elemtype(typeof(array))}]]"
						+ "\\/{null})) & ");
		if (mch)
			stream.println("!(name,dim).(name: " + defNAMES + " & (dim: INTEGER & 0<=dim & not(dim = 0)) "
							+ "=> subtypes[{name|->dim}] = {cc,dd | cc: " + defNAMES
							+ " & (dd: INTEGER & 0<=dd & not(dd = 0)) " + "& cc|->dd-1: subtypes[{name|->dim-1}]}) & ");
		else
			stream.println("!(name,dim).(name: " + defNAMES + " & (dim: INTEGER & 0<=dim & not(dim = 0)) "
							+ "=> subtypes[{name|->dim}] = SET(cc,dd).(cc: " + defNAMES
							+ " & (dd: INTEGER & 0<=dd & not(dd = 0)) " + "& cc|->dd-1: subtypes[{name|->dim-1}])) & ");

		if (mch)
			stream.println("flatran = %xx.(xx: REFERENCES +-> (t_int +-> REFERENCES) " + "| {yy | yy: REFERENCES "
							+ "& #zz.(zz: dom(xx) & yy: ran(xx(zz)))}) & ");
		else
			stream.println("flatran = %xx.(xx: REFERENCES +-> (t_int +-> REFERENCES) " + "| SET(yy).(yy: REFERENCES "
							+ "& #zz.(zz: dom(xx) & yy: ran(xx(zz))))) & ");
		stream.println("elemtype = %(name,dim).(name: " + defNAMES
						+ " & (dim: INTEGER & 0<=dim & not(dim = 0)) | name|->dim-1)");
	}

	/**
	 * Prints the part of the prelude concerning the properties of the builtin
	 * types and of the j_xxx functions.
	 */
	void printJvaluesProperties() {
		stream.println("c_minint: INTEGER & ");
		stream.println("c_maxint: INTEGER & ");
		stream.println("c_minshort: INTEGER & ");
		stream.println("c_maxshort: INTEGER & ");
		stream.println("c_minbyte: INTEGER & ");
		stream.println("c_maxbyte: INTEGER & ");
		stream.println("c_minchar: INTEGER & ");
		stream.println("c_maxchar: INTEGER & ");
		stream.println("c_minlong: INTEGER & ");
		stream.println("c_maxlong: INTEGER & ");
		stream.println("c_minint = -2147483647-1 & ");
		stream.println("c_maxint = 2147483647 & ");
		stream.println("c_maxshort = 32767 & ");
		stream.println("c_minshort = -32768 & ");
		stream.println("c_maxbyte = 127 & ");
		stream.println("c_minbyte = -128 & ");
		stream.println("c_minchar = 0 & ");
		stream.println("c_maxchar = 65535 & ");
		stream.println("t_int = -2147483647-1..2147483647 & ");
		stream.println("t_short = -32768..32767 & ");
		stream.println("t_byte = -128..127 & ");
		stream.println("t_char = 0..65535 & ");
		stream.println("t_long = c_minlong..c_maxlong & ");
		stream.println("j_add: t_int*t_int +-> t_int & ");
		stream.println("dom(j_add) = t_int*t_int & ");
		stream.println("j_sub: t_int*t_int +-> t_int & ");
		stream.println("dom(j_sub) = t_int*t_int & ");
		stream.println("j_mul: t_int*t_int +-> t_int & ");
		stream.println("dom(j_mul) = t_int*t_int & ");
		stream.println("j_div: t_int*(t_int-{0}) +-> t_int & ");
		stream.println("dom(j_div) = t_int*(t_int-{0}) & ");
		stream.println("j_rem: t_int*(t_int-{0}) +-> t_int & ");
		stream.println("dom(j_rem) = t_int*(t_int-{0}) & ");
		stream.println("j_neg: t_int +-> t_int & ");
		stream.println("dom(j_neg) = t_int & ");
		stream.println("j_shl: t_int*t_int +-> t_int & ");
		stream.println("dom(j_shl) = t_int*t_int & ");
		stream.println("j_shr: t_int*t_int +-> t_int & ");
		stream.println("dom(j_shr) = t_int*t_int & ");
		stream.println("j_ushr: t_int*t_int +-> t_int & ");
		stream.println("dom(j_ushr) = t_int*t_int & ");
		stream.println("j_and: t_int*t_int +-> t_int & ");
		stream.println("dom(j_and) = t_int*t_int & ");
		stream.println("j_or: t_int*t_int +-> t_int & ");
		stream.println("dom(j_or) = t_int*t_int & ");
		stream.println("j_xor: t_int*t_int +-> t_int & ");
		stream.println("dom(j_xor) = t_int*t_int & ");
		stream.println("j_int2char: t_int +-> t_char & ");
		stream.println("dom(j_int2char) = t_int & ");
		stream.println("j_int2byte: t_int +-> t_byte & ");
		stream.println("dom(j_int2byte) = t_int & ");
		stream.println("j_int2short: t_int +-> t_short & ");
		stream.println("dom(j_int2short) = t_int & ");
		stream.println("t_char<|j_int2char = id(t_char) & ");
		stream.println("t_byte<|j_int2byte = id(t_byte) & ");
		stream.println("t_short<|j_int2short = id(t_short) & ");
		stream.println("!ii.(ii: t_int => (0<=ii => " + "(ii mod 256<=127 => j_int2byte(ii) = ii mod 256) "
						+ "& (not(ii mod 256<=127) => j_int2byte(ii) = ii mod 256-256))" + " & (not(0<=ii) => "
						+ "j_int2byte(ii) = j_int2byte(ii+((-ii)/256+1)*256))) & ");
		stream.println("!ii.(ii: t_int => (0<=ii => (ii mod 65536<=32767 " + "=> j_int2short(ii) = ii mod 65536) "
						+ "& (not(ii mod 65536<=32767) " + "=> j_int2short(ii) = ii mod 65536-65536)) "
						+ "& (not(0<=ii) " + "=> j_int2short(ii) " + "= j_int2short(ii+((-ii)/65536+1)*65536))) & ");
		stream.println("j_int2char = %ii.(ii: t_int & 0<=ii | ii mod 65536)" + "<+%ii.(ii: t_int & not(0<=ii) "
						+ "| (ii+((-ii)/65536+1)*65536) mod 65536) & ");

	}

	public Enumeration getClasses() {
		bClasses = new Vector();
		AClassEnumeration ace = printer.getClasses();
		while (ace.hasMoreElements()) {
			AClass element = ace.nextElement();
			bClasses.add(new BClass(element));
		}
		return bClasses.elements();
	}

	/**
	 * @return
	 */
	public Enumeration getInterfaces() {
		bInterfaces = new Vector();
		AClassEnumeration ace = printer.getInterfaces();
		while (ace.hasMoreElements()) {
			AClass element = ace.nextElement();
			bInterfaces.add(new BClass(element));
		}
		return bInterfaces.elements();
	}

	static String arrayDecl(int tag) {
		switch (tag) {
			case Type.T_BOOLEAN :
				return "typeof~[{" + c_boolean + "|->1}] +-> (t_int +-> BOOL)";
			case Type.T_BYTE :
				return "typeof~[{" + c_byte + "|->1}] +-> (t_int +-> t_byte)";
			case Type.T_CHAR :
				return "typeof~[{" + c_char + "|->1}] +-> (t_int +-> t_char)";
			case Type.T_INT :
				return "typeof~[{" + c_int + "|->1}] +-> (t_int +-> t_int)";
			case Type.T_SHORT :
				return "typeof~[{" + c_short + "|->1}] +-> (t_int +-> t_short)";
			default :
				return null;
		}
	}

	static String arrayRefDecl(String r) {
		return "typeof~[" + defARRAYS + "-({" + c_int + "}\\/{" + c_char + "}\\/{" + c_short + "}\\/{" + c_byte
				+ "}\\/{" + c_boolean + "})*{1}] +-> (t_int +-> " + r + ")";
	}

}