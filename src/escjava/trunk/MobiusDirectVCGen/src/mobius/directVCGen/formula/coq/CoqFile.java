package mobius.directVCGen.formula.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;

import escjava.sortedProver.NodeBuilder.STerm;

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
		out.println("Lemma l:\n" + term + ".");
		out.println("Proof.");
		out.println("intros; repeat (split; intros).\n\nQed.");
	}
		
	public void finalize() {
		out.close();
	}
		
}
