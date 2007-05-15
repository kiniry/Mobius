package mobius.directVCGen.formula.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.Set;
import java.util.Vector;

import mobius.directVCGen.formula.Formula;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.NodeBuilder.FnSymbol;
import escjava.sortedProver.NodeBuilder.STerm;

/**
 * This class is used to print the proof obligations to a file Coq
 * would be able to handle. The path to bicolano is needed for 
 * everything to work.
 * @author J. Charles
 */
public class CoqFile {
	/** the stream to print to the target file */
	private PrintStream out;
	
	/** the name of the directory which contains bicolano's library files */
	private String base;
	
	/** the suffix used for the Coq files */
	public static final String suffix = ".v";
	
	
	/**
	 * Construct an object used to print a proof obligation in a file.
	 * @param configDir the library directory
	 * @param baseDir the directory where the generated file should be put 
	 * @param name the preferred name the file should have
	 * @throws FileNotFoundException if opening the file fails
	 */
	public CoqFile(File configDir, File baseDir, String name) throws FileNotFoundException {
		out = new PrintStream(new FileOutputStream(new File(baseDir, 
					name + suffix)));
		base = configDir.toString();
	}
	
	/**
	 * Write the proof obligation represented by the
	 * given term.
	 * @param term the formula representing the proof obligation
	 */
	public void writeProof(STerm term) {
		out.println("Lemma l:\n" + term + ".");
		out.println("Proof.");
		out.println("intros; repeat (split; intros).\n\nQed.");
	}
		
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#finalize()
	 */
	public void finalize() {
		out.close();
	}

	/**
	 * Write the definitions for coq: basically it writes class
	 * definitions; fields to declare; and special magickal symbols.
	 * @param symToDeclare Special relation symbols to declare
	 * @param fieldsToDeclare the fields to declare
	 * @param classNames the class names to declare
	 */
	public void writeDefs(Vector<FnSymbol> symToDeclare, Set<QuantVariable> fieldsToDeclare, Vector<String> classNames) {
		out.println("Add LoadPath \"" + base + "\".\n" +
			    "Add LoadPath \"" + base + File.separator + "Formalisation\".\n" +
	            "Add LoadPath \"" + base + File.separator + "Formalisation" +
										   File.separator + "Bicolano" + "\".\n" +
	            "Add LoadPath \"" + base + File.separator + "Formalisation" +
			   							   File.separator + "Library" + "\".\n" +
		        "Add LoadPath \"" + base + File.separator + "Formalisation" +
			   							   File.separator + "Library" + 
			   							   File.separator + "Map" + "\".\n");
		out.println("Load \"defs_types.v\".\n");
		for(String name: classNames) {
			out.println("Variable " + name + ": ClassName.");
		}
		out.println();
		for(QuantVariable field: fieldsToDeclare) {
			out.println("Variable " + CoqNodeBuilder.normalize(field.name) + ": FieldSignature.");
		}
		out.println();
		for(FnSymbol sym : symToDeclare) {
			out.print("Variable " + sym.name + ": ");
			STerm [] terms = Formula.generateTypes(sym.argumentTypes);
			for(STerm t: terms) {
				String str = t.toString();
				out.print(str + " -> ");
			}
			out.println(Formula.generateType(sym.retType) + ".");
		}
		out.println();

	}
		
}
