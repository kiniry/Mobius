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
import escjava.sortedProver.NodeBuilder.Sort;

public class CoqFile {
	PrintStream out;
	String base;
	public static final String suffix = ".v";
	public CoqFile(File configDir, File baseDir, String name) throws FileNotFoundException {
		out = new PrintStream(new FileOutputStream(new File(baseDir, 
					name + suffix)));
		base = configDir.toString();
	}
	
	
	public void writeProof(STerm term) {
		out.println("Lemma l:\n" + term + ".");
		out.println("Proof.");
		out.println("intros; repeat (split; intros).\n\nQed.");
	}
		
	public void finalize() {
		out.close();
	}


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

			for(Sort s: sym.argumentTypes) {
				String str = Formula.getCurrentLifter().builder.buildSort(s).toString();
				out.print(str + " -> ");
			}
			out.println(Formula.getCurrentLifter().builder.buildSort(sym.retType) + ".");
		}
		out.println();

	}
		
}
