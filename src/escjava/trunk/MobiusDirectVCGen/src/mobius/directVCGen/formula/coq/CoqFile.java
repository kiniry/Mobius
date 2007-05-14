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

// TODO: add comments
public class CoqFile {
	// TODO: add comments
	PrintStream out;
	// TODO: add comments
	String base;
	// TODO: add comments
	public static final String suffix = ".v";
	
	
	// TODO: add comments
	public CoqFile(File configDir, File baseDir, String name) throws FileNotFoundException {
		out = new PrintStream(new FileOutputStream(new File(baseDir, 
					name + suffix)));
		base = configDir.toString();
	}
	
	// TODO: add comments
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

	// TODO: add comments
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
