/*
 * Created on Mar 8, 2005
 */
package coqPlugin;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;

import jpov.structure.Goal;
import jpov.structure.Lemma;

/**
 * The CoqFile class contains data representing a coqfile. For now the 
 * representation is very simple, without subtleties.
 * @author jcharles
 */
public class CoqFile {
	String beginning = "";
	String proof = "";
	String end= "";

	
	/**
	 * A simple constructor.
	 */
	public CoqFile() {
	}
	
	/**
	 * Load the coq file from the file which is the parameter.
	 * @param file the file to transform to a coqfile.
	 */
	public CoqFile(File file) {
		try {
			LineNumberReader in = new LineNumberReader(new FileReader(file));
			String str;
			StringBuffer bg = new StringBuffer("");
			StringBuffer pr = new StringBuffer("");
			StringBuffer en = new StringBuffer("");
			while ((str = in.readLine()) != null) {
				bg.append(str + "\n");
				if(str.startsWith("Proof with")) {
					while ((str = in.readLine()) != null) {
						if(str.startsWith("Qed.")) {
							while ((str = in.readLine()) != null) {
								en.append(str+"\n");
							}
						}
						else {
							pr.append(str + "\n");
						}
						
					}
				}
				
			}
			beginning = bg.toString();
			proof = pr.toString();
			end = en.toString();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}


	
//	/**
//	 * Load a coqfile from the inputstream.
//	 * @deprecated because
//	 * @param s the input stream
//	 * @return the loaded coqfile
//	 * @throws IOException if there was a problem
//	 */
//	public static CoqFile load(JpoInputStream s) throws IOException {
//		return new CoqFile(s);
//	}
	
//	/**
//	 * Save the CoqFile to an outputstream.
//	 * @deprecated because
//	 * @param s the output stream
//	 * @throws IOException if there was a problem
//	 */
//	public void save(JpoOutputStream s) throws IOException {
//		s.writeUTF(proof);
//	}
	
	public String toString() {
		return beginning + proof + end;
	}
	
	public String getProof() {
		return proof;
	}
	public static String getNameFromGoal(Goal g) {
		Lemma l = (Lemma)g.getParent();
		int gnum = 0;
		for(gnum = 1; gnum <l.getGoals().length; gnum++) {
			if(l.getGoals()[gnum -1] == g)
				break;
		}
		String beg = l.getName().replace('_', '.');
		if(beg.length() > 2) {
			beg.substring(2);
		}
		else {
			beg = "method_" + beg;
		}
		beg.replaceAll("method\\.", "method_");
		return beg + "-" + l.getNum() + "-"+ (gnum) + ".v";
	}
}
