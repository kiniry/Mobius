package coqPlugin.printers;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import jml2b.IJml2bConfiguration;
import jml2b.pog.printers.AClassEnumeration;
import jml2b.pog.printers.IClassResolver;
import jml2b.pog.printers.IPrinter;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Type;

public class PreludeSubtypes extends Printer{
	private IClassResolver printer;
	private String[] builtinNames = IPrinter.builtinNames;
	private String outDir;
	private Printer preludeClasses;
	
	
	public PreludeSubtypes(Printer preludeClasses, File output_directory, String name, IClassResolver printer, IJml2bConfiguration config)
		throws IOException {
		super(output_directory, name + "_subtypes.v");
		this.printer = printer;
		
		outDir = output_directory.toString();
		setModule(name + "Subtypes");

		this.preludeClasses = preludeClasses;
		
		startWriting(config);
 	}
	
	
	public boolean mustRewrite() {
		return true;
	}

	protected void writeToFile(PrintStream stream, IJml2bConfiguration config) {
		stream.println("Add LoadPath \"" + outDir + "\".\n");
		
		stream.println("Require Import \"" + StaticPrelude2.fileName + "\".");
		stream.println("Require Import \"" + preludeClasses.getNameWithoutExtension() + "\".");
		stream.println("Import " + preludeClasses.getModule() + ".\n");
		

		stream.println("Module " + getModule() + ".");
		stream.println("Module JackClasses := " + StaticPrelude2.moduleName + " " + preludeClasses.getModule() +".");
		stream.println("Import JackClasses.");
		
		defineLocal(stream, config);
		print_subtypes_axioms(stream);
		
		defineSubtypesHints(stream, config);
		stream.println("End " + getModule() + ".");
		
	}
	


	private void defineSubtypesHints(PrintStream stream, IJml2bConfiguration config) {
		int count = 0;
		count = defineSubtypesHints(stream, printer.getClasses(), count, config);
		count = defineSubtypesHints(stream, printer.getInterfaces(), count, config);
		stream.print("Hint Resolve");
		for (int i = 0; i < count; i++) {
			stream.print(" subtypes_" + i);
		}
		stream.println(".");
	}
	private int defineSubtypesHints(PrintStream stream,
			AClassEnumeration e, int count, IJml2bConfiguration config) {
		while(e.hasMoreElements()) {
			AClass c = e.nextElement();
			if(c.getModifiers().isNative())
				continue;
			count = defineSubtypesHints(stream, printer.getClasses(), c, count, config);
			count = defineSubtypesHints(stream, printer.getInterfaces(), c, count, config);
		}
		return count;
	}
	private int defineSubtypesHints(PrintStream stream,
			AClassEnumeration e,
			AClass c,
			int count, IJml2bConfiguration config) {
			Type c_type = new Type(c);

			while (e.hasMoreElements()) {
				AClass subtype = (AClass) e.nextElement();
				if(subtype.getModifiers().isNative())
					continue;
				String c2 = "(class " + c.getBName() + ")";
				String c1 = "(class " + subtype.getBName() + ")";
				if(c1.equals(c2))
					continue;
				Type s_type = new Type(subtype);
				if(s_type.isSubtypeOf(config, c_type)) { 
					stream.println("Lemma subtypes_" + count++ + ": forall c: Types, " +
							"subtypes c " + c1 + " -> " +
							"subtypes c " + c2 + ".");
					stream.print("Proof ");
					stream.println("(fun (c:Types) (h1: subtypes c " + c1 + ") => ");
					stream.print("        subtypes_trans " + c2 + " " + c1 + "  I c h1)");
					//stream.println(": forall c: Types, " +
					//"subtypes c " + c1 + " -> " +
					//"subtypes c " + c2);
					//stream.println("Proof.\nintros c h1.");
					//stream.println("assert(h2 : subtypes " + c1 + " " + c2 + ").");
					//stream.println("unfold subtypes; trivial.");
					//stream.println("assert ( h:= subtypes_trans " + c2 + " " + c1 + " h2 c h1); trivial.");
					stream.println(".\n");
				}
				
			}
			return count;
		}

	/**
	 * Prints the subtypes valuation
	 * @param config The current configuration
	 **/
	private void defineSubtypes(PrintStream stream, IJml2bConfiguration config) {
		// print subtypes for builtin types
		for (int i = 0; i < builtinNames.length; ++i) {
			String builtin_name = builtinNames[i];
			if (i != 0)
				stream.print("     | ");
			else
				stream.print("      ");
			stream.println("(class " + builtin_name + ") => match t1 with");
			stream.println("        (class " + builtin_name + ") => True");
			stream.println("        | _ => False");
			stream.println("        end");
		}
		defineSubtypes(stream, printer.getClasses(), config);
		defineSubtypes(stream, printer.getInterfaces(), config);

	}
	
	
	static private void print_subtypes_axioms(PrintStream s){
		s.println("Axiom subtypes_trans :\n" + 
			"forall a b , subtypes b a  -> forall c, subtypes c b -> subtypes  c a. \n");

		s.println("(* The Proof is too long to compute so.... forall a b , subtypes b a  -> forall c, subtypes c b -> subtypes  c a.)\nProof.\n" +
				"destruct a. destruct b.\n" + 
				"2:\n" +
				"simpl in hyp2;\n" +
				"rewrite <- hyp2 in hyp1; trivial.\n" +
				"2:\n" +
				"simpl in hyp1;\n" +
				"rewrite hyp1 in hyp2; trivial.\n" +
				"destruct c.\n" +
				"2:\n" +
				"simpl in hyp2;\n" +
				"destruct c1; elim hyp2; auto.\n\n" +
				"destruct c1; \n" +
				"destruct c0;try (elim hyp1;fail);\n" +
				"destruct c;\n" +
				"try (elim hyp2; fail); trivial." +
				"Qed. *)\n");

		s.println("Lemma subtypes_refl:" +
				"forall  a, subtypes  a a.\n" +
				"Proof.\n" +
				"intros.  destruct a.\n" +
				"destruct c; simpl; trivial.\n" +
				"simpl; trivial.\n" +
				"Qed.\n");


	}
	/**
	 * Prints the subtypes definition and the field declaration.
	 * @param stream
	 * @param config The current configuration
	 **/
	private void defineLocal(PrintStream stream, IJml2bConfiguration config){
		stream.println("\nDefinition subtypes (t1: Types) (t2: Types): Prop :=");
		stream.println("    match t2 with");
		defineSubtypes(stream, config);
		stream.println("   | _ => t1 = t2");
		stream.println("   end.\n");

	}
	/**
	 * Prints the subtypes valuation for a set of classes
	 * @param config The current configuration
	 * @param e The set of classes
	 **/
	private void defineSubtypes(PrintStream stream, AClassEnumeration e, IJml2bConfiguration config) {
		while (e.hasMoreElements()) {
			AClass c = e.nextElement();
			if(c.getModifiers().isNative())
				continue;
			stream.println(
				"     | (class " + c.getBName() + ") => match t1 with");

			if (c.isObject()) {
				stream.println("        _ => True");
				stream.println("        end");
			} else {
				boolean is_first =
					defineSubtypesOf(stream, printer.getClasses(), c, true, config);
				defineSubtypesOf(stream, printer.getInterfaces(), c, is_first, config);

				if (c.equals("java.lang.Cloneable")
					|| c.equals("java.io.Serializable")) {
					stream.println("        | (array _ _) => True");
				}
				stream.println("        | _ => False");
				stream.println("        end");
			}
		}
	}

	/**
	 * Prints the subtypes valuation for a class
	 * @param config The current configuration
	 * @param e The current set of classes
	 * @param c The class
	 **/
	private boolean defineSubtypesOf(PrintStream stream,
		AClassEnumeration e,
		AClass c,
		boolean is_first, IJml2bConfiguration config) {
		Type c_type = new Type(c);

		while (e.hasMoreElements()) {
			AClass subtype = (AClass) e.nextElement();
			Type s_type = new Type(subtype);
			if(subtype.getModifiers().isNative())
				continue;
			if (s_type.isSubtypeOf(config, c_type)) {
				if (is_first) {
					is_first = false;
					stream.print("         ");
				} else {
					stream.print("        | ");
				}
				stream.println("(class " + subtype.getBName() + ") => True");
			}
		}
		return is_first;
	}
}
