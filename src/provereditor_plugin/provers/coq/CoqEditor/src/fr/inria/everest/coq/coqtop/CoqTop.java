/*
 * Created on Mar 3, 2005
 */
package fr.inria.everest.coq.coqtop;

import java.io.IOException;
import java.io.LineNumberReader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.LinkedList;

import prover.exec.ITopLevel;
import prover.exec.toplevel.exceptions.ProverException;
import prover.exec.toplevel.exceptions.IncompleteProofException;
import prover.exec.toplevel.exceptions.SyntaxErrorException;



/**
 * The class CoqTop contains those higher level interactions with coq.
 * @author J. Charles
 */

public class CoqTop extends Coq implements ITopLevel{
	private LinkedList sections = new LinkedList();
	private LinkedList lemmas = new LinkedList();


	/**
	 * The simple constructor.
	 * @throws ProverException if it is unable to build the coq process.
	 */
	public CoqTop (String strCoqTop, String [] path) throws ProverException {
		super(strCoqTop, path, 100);
	}
	
	public ITopLevel createTopLevel (String strCoqTop, String [] path) throws ProverException {
		return new CoqTop(strCoqTop, path);
		
	}
	
	/**
	 * The one arg constructor.
	 * @param iGraceTime The grace time for TopLevel
	 * @throws ProverException if it is unable to build the coq process.
	 */
	public CoqTop (String strCoqTop, String [] path, int iGraceTime) throws ProverException {
		super(strCoqTop, path, iGraceTime);
	}
	
	
	/**
	 * Send the command to start a new section in coq.
	 * @param name the name of the section
	 * @throws ProverException if there is an unexpected problem.
	 */
	public void startSection(String name) throws ProverException {
		sections.addFirst(name);
		sendCommand("Section " + name + ".");
	}
	
	
	/**
	 * Send the command to end a section in coq. 
	 * It checks if the section can be closed.
	 * @param name the name of the section
	 * @throws ProverException if there is an unexpected problem or 
	 *                      if it is asked to close the wrong section.
	 */
	public void endSection(String name) throws ProverException {
		String s = (String) sections.removeFirst();
		if (s.equals(name)) {
			sendCommand("End " + name + ".");
		} else {
			sections.addFirst(s);
			throw new ProverException("Bad section close operation: you should have closed section " + s + ".");
		}
	}
	
	/**
	 * Reset the named section and also erase it.
	 * It checks if the section can be reset.
	 * @param name the name of the section
	 * @throws ProverException if there is an unexpected problem or 
	 *                      if it is asked to reset the wrong section.
	 */
	public void resetSection(String name) throws ProverException {
		String s = (String) sections.removeFirst();
		if (s.equals(name)) {
			sendCommand("Reset " + name + ".");
		} else {
			sections.addFirst(s);
			throw new ProverException("Bad section reset operation: you should have closed section " + s + ".");
		}
	}
	
	/**
	 * Starts a new lemma; and send the commande Proof to Coqtop.
	 * @param name name of the lemma
	 * @param body body of the lemma
	 * @throws ProverException if there is an unexpected problem
	 */
	public void declareLemma(String name, String body) throws ProverException {
		sendCommand("Lemma " + name +": " + body + ".");
		sendCommand("Proof.");
		lemmas.addFirst(name);
	}
	/**
	 * Starts a new lemma; and send the commande Proof to Coqtop.
	 * @param name name of the lemma
	 * @param body body of the lemma
	 * @throws ProverException if there is an unexpected problem
	 */
	public void declareLemma(String name, String body, String thing) throws ProverException {
		sendCommand("Lemma " + name +": " + body + ".");
		sendCommand("Proof with " + thing);
		lemmas.addFirst(name);
	}
	
	
	/**
	 * Restart the current proof.
	 * @throws ProverException if there is an unexpected problem
	 */
	public void restart() throws ProverException {
		sendCommand("Restart.");
	}
	
	

	
	/**
	 * Send the command Proof to coq. I wonder who will use it.
	 * @throws ProverException if there is an unexpected problem
	 */
	public void proof() throws ProverException {
		sendCommand("Proof.");
	}
	
	
	/**
	 * Send the given command to coqtop. A command is a sentence which ends with a dot.
	 * @param s The command to send
	 * @throws SyntaxErrorException If coq yells about a syntax error.
	 * @throws ProverException if there is an unexpected problem
	 */
	public void sendCommand(String s) throws ProverException {
		super.sendCommand(s);
		String str = getBuffer().toString();
		if(str.indexOf("Syntax error: ") != -1)
			throw new SyntaxErrorException(str.toString());
		if(str.indexOf("Error:") != -1)
			throw new SyntaxErrorException(str.toString());
		if(str.indexOf("Anomaly:") != -1)
			throw new SyntaxErrorException(str.toString());
		if(str.startsWith("Toplevel input") || str.indexOf("User error") != -1)
			throw new ProverException("An error occured during the proof:\n" + str + "\n");
	}
	
	/**
	 * Give the translation of the last object sent to CoqTop.
	 * @return A pretty print of the last object.
	 * @throws SyntaxErrorException If coq yells about a syntax error.
	 * @throws ProverException if there is an unexpected problem
	 * @throws IOException If there is a failure
	 */
	public String inspect() throws ProverException, IOException {
		super.sendCommand("Inspect 1.");
		String str;
		str = getBuffer().toString();
//		while(str.indexOf("*** [") == -1){
//			waitForMoreInput();
//			str = getBuffer().toString();
//		}
		if(str.indexOf("Syntax error: ") != -1)
			throw new SyntaxErrorException(str.toString());
		if(str.indexOf("Error:") != -1)
			throw new SyntaxErrorException(str.toString());
		if(str.startsWith("Toplevel input") || str.indexOf("User error") != -1)
			throw new ProverException("An error occured during the proof:\n" + str + "\n");
		return str;
	}
	
	

	
	
	/**
	 * Send the Qed command to TopLevel.
	 * @throws IncompleteProofException If the proof you are trying to save is incomplete.
	 * @throws ProverException if there is an unexpected problem
	 */
	public void qed() throws ProverException {
		super.sendCommand("Qed.");
		while ((getBuffer().indexOf("User error: Attempt to save an incomplete proof") == -1) &&
				(getBuffer().indexOf("is defined")) == -1){
			// we wait for a cool output...
			try {
				waitForMoreInput();
			} catch (IOException e) {
				// this should not happen
				e.printStackTrace();
			}
		}
		
		if(getBuffer().indexOf("is defined") != -1) {
			// which output did we get?
			lemmas.removeFirst();
		} else {
			throw new IncompleteProofException(getBuffer());
		}
	}
	
	
	/**
	 * Is there any lemmas which are not proven yet?
	 * @return true if there are some pending lemmas.
	 */
	public boolean hasPendingLemmas() {
		return !lemmas.isEmpty();
	}
	
	
	/**
	 * Pretty print the sections.
	 * @param i internal use - if called should be sections.size()
	 * @param indent some spaces
	 * @return the pretty printed sections
	 */
	private String printSections(int i, String indent) {
		String s;
		if (i > 0) {
			s = indent + sections.get(i - 1) + " {\n" + 
				indent + printSections(i - 1, indent + "   ")  + "\n" +
				indent + "}";
		}
		else {
			s = indent + printLemmas(lemmas.size());
		}
		return s;
	}
	
	/**
	 * Pretty print the lemmas.
	 * @param i internal use - if called should be lemmas.size()
	 * @return the pretty printed lemmas
	 */
	private String printLemmas(int i) {
		String s = "";
		if (i > 0) {
			s = "[" + lemmas.get(i - 1) + " " + 
				printLemmas(i - 1) + "] ";
		}
		return s;
	}
	
	/**
	 * Prints the current state (more or less) of CoqTop.
	 * @return A string representing an internal state.
	 */
	public String toString() {
		return "CoqTop State: \n" + printSections(sections.size(), "   "); 
	}
	

	
	/**
	 * Send the command Show Intros to coqtop and return the list of the 
	 * identifiers to introduce  
	 * @return The list of identifiers
	 * @throws ProverException 
	 */
	public String [] showIntros() throws ProverException {
		clearBuffer();
		sendCommand("Show Intros.");
		String buff = getBuffer().replaceAll("\n", " ");
		return buff.split(" +");
	}

	public String [] show() throws ProverException, IOException{
		clearBuffer();
		super.sendCommand("Show.");
		String str;
		str = getBuffer();
		while(str.indexOf("========\n") == -1){
			waitForMoreInput();
			str = getBuffer();
		}
		if(str.indexOf("Syntax error: ") != -1)
			throw new SyntaxErrorException(str.toString());
		if(str.indexOf("Error:") != -1)
			throw new SyntaxErrorException(str.toString());
		if(str.startsWith("Toplevel input") || str.indexOf("User error") != -1)
			throw new ProverException("An error occured during the proof:\n" + str + "\n");
		
		LineNumberReader lnr = new LineNumberReader(new StringReader(str.toString()));
		ArrayList al = new ArrayList();
		String curr = "";
		while((str = lnr.readLine()) != null) {
			if (str.indexOf("=========") != -1) {
				al.add(curr);
				str = "";
				curr = lnr.readLine();
				break;
			}
			else if (str.matches("^  [a-zA-Z_0-9]+ : .*")) {
				al.add(curr);
				curr = str;
			}
			else {
				curr += "\n" + str;
			}
		}
		while((str = lnr.readLine()) != null) {
			curr += "\n" + str;
		}
		al.add(curr);
		String [] arr = new String [al.size()];
		Object[] t = al.toArray();
		for(int i = 0; i < t.length; i++) arr[i] = (String)t[i];
		return arr;
	}
	
	/**
	 * Undo n vernac commands or n tactics if we are in proof mode.
	 * @param steps the number of vernacs to undo.
	 * @throws ProverException if there is an unexpected problem
	 */
	public void undo(int steps) throws ProverException {
		
		int step = getStep();
		int last = getProofStep();
		if(step > 0) {//we have the right version *cvs* of coq
			if((last == 1)){ //&& isProofMode()) {
				abort();
			} else
			if(last >0) {
				
				try {
					sendCommand("Undo " + steps + ".");
				}
				catch (Exception e) {
					sendCommand("Back " + steps + ".");
				}
			}
			else {
				sendCommand("Back " + steps + ".");
			}
		}
		else
			if(isProofMode())
				sendCommand("Undo " + steps + ".");
			else
				sendCommand("Back " + steps + ".");
	}
	
	
	/**
	 * Abort the current proof.
	 * @throws ProverException if there is an unexpected problem
	 */
	public void abort() throws ProverException {
		sendCommand("Abort.");	
	}

	public String print(String nom) throws ProverException, IOException{
		super.sendCommand("Print " + nom +".");
		String str;
		str = getBuffer().toString();
//		while(str.indexOf("*** [") == -1){
//			waitForMoreInput();
//			str = getBuffer().toString();
//		}
		if(str.indexOf("Syntax error: ") != -1)
			throw new SyntaxErrorException(str.toString());
		if(str.indexOf("Error:") != -1)
			throw new SyntaxErrorException(str.toString());
		if(str.startsWith("Toplevel input") || str.indexOf("User error") != -1)
			throw new ProverException("An error occured during the proof:\n" + str + "\n");
		return str;
	}
}
