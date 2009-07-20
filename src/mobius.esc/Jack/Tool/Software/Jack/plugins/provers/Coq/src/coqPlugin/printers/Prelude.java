/*
 * Created on Feb 28, 2005
 *
 */
package coqPlugin.printers;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Enumeration;

import prover.plugins.exceptions.ProverException;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.pog.printers.AClassEnumeration;
import jml2b.pog.printers.IClassResolver;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.AField;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Type;
import coqPlugin.language.CoqType;

/**
 * @author jcharles
 *
 */
public class Prelude extends Printer{
	private Printer helper1 ,  helper2, helper3, preludeClasses, preludeSubtypes;
	private IClassResolver printer;
	private String outDir;
	
	public boolean mustRewrite() {
		return true;
	}
	
	/**
	 * @param output_directory
	 * @param name
	 * @param config
	 */
	public Prelude(File output_directory, String name, IClassResolver printer, IJml2bConfiguration config)
			throws IOException {
		
		super(output_directory, name);
		outDir = output_directory.toString();
		this.printer = printer;
		helper1 = new StaticPrelude1(output_directory, config);
		helper2 = new StaticPrelude2(output_directory, config);
		helper3 = new LocalTactics(output_directory, config);	
		preludeClasses = new PreludeClasses(output_directory, getNameWithoutExtension(),
				printer, config);
		preludeSubtypes = new PreludeSubtypes(preludeClasses, 
				output_directory, 
				this.getNameWithoutExtension(), printer, config);
		new UserExtensions(output_directory, config);
		startWriting(config);
	}


	/* (non-Javadoc)
	 * @see coqPlugin.printers.Printer#writeToFile(java.io.PrintStream)
	 */
	protected void writeToFile(PrintStream stream, IJml2bConfiguration config) {

		printVernac(stream, config);
		
	}
	
	/**
	  * Prints the prelude in a vernacular file
	 * @param 
	 * @param stream
	 * @param config
	  * @param config The current configuration
	  **/
	void printVernac(PrintStream stream, IJml2bConfiguration config) {
		stream.println("Add LoadPath \"" + outDir + "\".\n");
		stream.println("Require Import ZArith.");
		stream.println("Require Import \"" + 
				helper1.getNameWithoutExtension() + "\".");
		stream.println("Require Import \"" + 
						helper2.getNameWithoutExtension() + "\".");
		stream.println("Require Import \"" + 
				preludeClasses.getNameWithoutExtension() + "\".\n");
		stream.println("Require Import \"" + 
				preludeSubtypes.getNameWithoutExtension() + "\".\n");
		
		stream.println("Module JackLogic.");
		stream.println("Module JackClasses := " + StaticPrelude2.moduleName + " " + preludeClasses.getModule() + ".\n");

		stream.println("(* Importing Jack arithmetic and classes *)");
		stream.println("Import " + StaticPrelude1.moduleName + ".");
		stream.println("Import JackClasses.");
		stream.println("Import " + preludeClasses.getModule() + ".");
		stream.println("Import "+ preludeSubtypes.getModule() + ".\n");
		
		stream.println("Export " + StaticPrelude1.moduleName + ".");
		stream.println("Export JackClasses.");
		stream.println("Export " + preludeClasses.getModule() + ".");
		stream.println("Export "+ preludeSubtypes.getModule() + ".");
		
//		stream.println("Export JackArith.");
//		stream.println("Export JackClasses.\n");
		
		stream.println("\n(* Some more array things *)");
		stream.println( "Lemma j_le_lt_or_eq: forall n m:Z, n <= m -> n < m \\/ n = m.\n"+
						"Proof.\n"+
						"unfold j_le, j_lt. intros; omega.\n"+
						"Qed.\n");
		stream.println(
				"Axiom ArrayTypeAx :\n" +
				"forall arr c n,  (subtypes (typeof arr) (array (class c) n)) -> \n" +
				"     forall pos, subtypes (typeof (refelements arr pos)) (class c).\n\n" +
				"Axiom arraylenAx : forall a c n, instances a -> subtypes (typeof a) (array c n) -> j_le 0 (arraylength a).\n");
		stream.println("\n(* Fields definitions *)");
		printFieldTypes(stream);
		
		stream.println("\n\nLoad \"" + helper3.getAbsolutePath() + "\".");
		
		stream.println("End JackLogic.\n");
	}













	/**
	 * Prints a field declaration 
	 * @param f The field
	 **/
	void printFieldType(PrintStream stream, AField f) {
		if (f.garbage) {
			// ignore fields which do not appear in lemmas
			return;
		}
		if(f.getModifiers().isGhost() || f.getModifiers().isModel()) {
			if(f.getType().getRefType() != null) {
				if(f.getType().getRefType().getModifiers().isNative())
				return; 	
			}
			
		}
	
		if (f.isExpanded())
			return;

		// get the type of the field
		Type t = f.getType();

		if (t.getTag() == Type.T_DOUBLE || t.getTag() == Type.T_LONG)
			return; // bad sign...

		
		if (f.getModifiers().isStatic()) {
			// static field
			String str = "Definition f_"
				+ IdentifierResolver.getAbsoluteName(f) + "_type"
				+ " := "
				+ getCoqSuperType(t.getTag())
				+ ".\n";
			str += "Variable "
				+ f.getBName()
				+ " : f_"
				+ IdentifierResolver.getAbsoluteName(f) + "_type" 
				+ ".\n";
			str += "Definition "
				+ f.getBName()
				+ "Dom (n:" + getCoqSuperType(t.getTag()) + "): Prop := " 
				+ getFieldDom(f.getBName(), t)
				+ ".";
		
			stream.println(str);
			if ((t.getTag() == Type.T_REF) || (t.getTag() == Type.T_ARRAY))
				stream.println(
						"Axiom "
						+ f.getBName()
						+ "Ran : " 
						+ " ((instances " + f.getBName() + ") \\/ (" + f.getBName() + "  = null))"
							+ ".");
		} else {
			// member field
			stream.println(
				"Definition f_" + IdentifierResolver.getAbsoluteName(f) + "_type := " + 
					CoqType.Reference + " -> " + getCoqSuperType(t.getTag()) + ".");
			stream.println("Variable " + f.getBName() + " : f_" + IdentifierResolver.getAbsoluteName(f) + "_type.\n");
			stream.println(
					"Axiom "
						+ f.getBName()
						+ "Dom : forall (n: "+ CoqType.Reference + "), " 
						+ getFieldDom("(" + f.getBName() + " n)", t) + " <-> "
						+ "subtypes (typeof n) (class " + f.getDefiningClass().getBName() + ")"
						+ ".");
			if ((t.getTag() == Type.T_REF) || (t.getTag() == Type.T_ARRAY))
				stream.println(
						"Axiom "
							+ f.getBName()
							+ "Ran : forall (n: "+ CoqType.Reference + "), " 
							+ "n <> null -> subtypes (typeof n) (class " + f.getDefiningClass().getBName() + ")" 
							+ " -> ((instances (" + f.getBName() + " n)) \\/ ((" + f.getBName() + " n) = null))"
							+ ".");
			
			/*			stream.println(
				"Axiom "
					+ f.getBName()
					+ "Dom : (r: "+ CoqType.Reference + ") "
					+ getFieldDom("r", new Type(f.getDefiningClass()))
					+ " <-> (dom "+ CoqType.Reference + ""
					+ getCoqSuperType(t.getTag())
					+ " "
					+ f.getBName()
					+ " r).");*/
/*			stream.println(
				"Axiom "
					+ f.getBName()
					+ "Ran : forall r:"+ CoqType.Reference + ", "
					+ getFieldDom("(" + f.getBName() + " r)", t)
					+ ".");*/
		}
	}

	/** Prints fields type declaration.
	* @param e The set of fields
	**/
	private void printFieldTypes(PrintStream stream, Enumeration e) {
		while (e.hasMoreElements()) {
			AField f = (AField) e.nextElement();
			printFieldType(stream, f);
		}
	}

	/**
		* Prints the fields of a set of classes type declaration.
		* @param e The set of classes
		**/
	private void printFieldTypesForClasses(PrintStream stream, AClassEnumeration e) {
		while (e.hasMoreElements()) {
			AClass c = e.nextElement();
			printFieldTypes(stream, c.getFields());
		}
	}

	/**
		* Prints the field type declaration
		**/
	private void printFieldTypes(PrintStream stream) {
		//firstItem = true;
		printFieldTypesForClasses(stream, printer.getClasses());
		printFieldTypesForClasses(stream, printer.getInterfaces());
	}

	/**
	 * Returns the super type of a type
	 * @param tag The tag associated to a type
	 * @return The Cop type
	 **/
	static public String getCoqSuperType(int tag) {
		switch (tag) {
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
			case Type.T_ARRAY :
				return CoqType.Reference;
			default :
				throw new InternalError(
					"Unhandled case in "
						+ "FilePrinter.getCoqSuperType(Type):"
						+ tag);
		}
	}

	/**
	 * Returns the formula corresponding to the domain of a field
	 * @param f The field
	 * @param t The field type
	 **/
	private String getFieldDom(String f, Type t) {
		switch (t.getTag()) {
			case Type.T_INT :
				return "(t_intDom " + f + ")";
			case Type.T_SHORT :
				return "(t_shortDom " + f + ")";
			case Type.T_CHAR :
				return "(t_charDom " + f + ")";
			case Type.T_BYTE :
				return "(t_byteDom " + f + ")";
			case Type.T_BOOLEAN :
				return "True";
			case Type.T_REF :
			case Type.T_ARRAY :
				return "(subtypes (typeof " + f + ")" + getCoqType(t) + ")";
			default :
				throw new InternalError(
					"Unhandled case in "
						+ "FilePrinter.getFieldDom(String, Type)");
		}
	}

	/**
	 * Converts a type into Coq
	 * @param t The type
	 * @return The corresponding Cop type
	 **/
	static private String getCoqType(Type t) {
		switch (t.getTag()) {
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
				return "(class " + t.getRefType().getBName() + ")";
			case Type.T_ARRAY :
				return "(array "
					+ getArrayClass(t)
					+ " "
					+ t.getDimension()
					+ ")";
			default :
				throw new InternalError(
					"Unhandled case in " + "FilePrinter.getCoqType(Type)");
		}
	}

	/**
	 * Returns the class of the element of an array
	 * @param t The arary type
	 **/
	static private String getArrayClass(Type t) {
		switch (t.getTag()) {
			case Type.T_INT :
				return "(class c_int)";
			case Type.T_SHORT :
				return "(class c_short)";
			case Type.T_CHAR :
				return "(class c_char)";
			case Type.T_BYTE :
				return "(class c_byte)";
			case Type.T_BOOLEAN :
				return "(class c_boolean)";
			case Type.T_REF :
				return "(class " + t.getRefType().getBName() + ")";
			case Type.T_ARRAY :
				return getArrayClass(t.getElemType());
			default :
				throw new InternalError(
					"Unhandled case in " + "FilePrinter.getArrayClass(Type)");
		}
	}


		public void compile() throws ProverException {
			helper1.compile();
			helper2.compile();
			preludeClasses.compile();
			preludeSubtypes.compile();
			super.compile();
		}


}
