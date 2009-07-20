package coqPlugin.prooftask.util;

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;

import prover.exec.AProverException;
import coqPlugin.PreferencePage;
import fr.inria.everest.coq.sugar.CoqTop;
import fr.inria.everest.coq.sugar.CoqUtils;

public class CoqPrintStream extends PrintStream {
	CoqTop ct;
	private boolean prettyprint = false; 
	public CoqPrintStream(OutputStream out) throws AProverException {
		super(out);
		prettyprint = PreferencePage.getCoqPrettyPrint();
		if(prettyprint) {
			ct = CoqUtils.createNewCoqTop(); 
			ct.restart();
		}
	}
	public String prettyprint(String prefix, String s) throws AProverException, IOException {
		String out = s;
		if(prettyprint) {
			ct.clearBuffer();
			ct.sendCommand(s);
			String s2 = ct.inspect();
			
			if(prefix.trim().equals("Definition")) {
				String nom = s2.substring(0, s2.indexOf(": "));
				String s4 = ct.print(nom);
				int ind;
				s4 = ((ind = s4.lastIndexOf("\n\nArgument scopes")) != -1) ? s4.substring(0, ind) : s4;
				out = prefix + s4.replaceFirst("=", ":=").substring(0, s4.lastIndexOf(":") + 1).trim() + ".";
			}
			else {
				int ind = ((ind = s2.lastIndexOf("]\n\nArgument scopes")) == -1)? s2.lastIndexOf("]") : ind; 
			
				String s3 = s2.substring(s2.lastIndexOf("*** [") + 5, ind);

				out = prefix + s3.trim() + ".";
			}
			super.println(out);
			
		}
		else 
			super.println(s);
		return out;
	}
	public void pp_goal(String s) throws AProverException, IOException{
		if(!prettyprint) {
			super.println(s);
			return;
		}
		ct.sendCommand(s);
		String [] arr = ct.show();
		super.println("Lemma l: \n" + arr[arr.length - 1] + ".");
		/*// this is bad bad bad bad....
		String [] vars = ct.showIntros(); 
		ct.sendCommand("intros.");
		String [] arr = ct.show();
		super.println("\n(* The introduced lemma. *)");
		for (int i = vars.length; i > 0; i--) {
			super.println("Variable " + arr[arr.length - i - 1] + ".");
		}
		
		super.println("Lemma l: \n" + arr[arr.length - 1] + ".");
		*/
	}
	public void println(String s) {
		if(prettyprint) {
			try {
				ct.sendCommand(s);
			} catch (AProverException e) {
				e.printStackTrace();
			}
		}
		super.println(s);
	}

	public void simplprint(String s) {
		super.println(s);
	}
}
