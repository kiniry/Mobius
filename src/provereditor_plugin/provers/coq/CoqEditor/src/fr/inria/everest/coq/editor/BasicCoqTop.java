/*
 * Created on Mar 3, 2005
 */
package fr.inria.everest.coq.editor;

import java.util.LinkedList;

import prover.exec.ITopLevel;
import prover.exec.toplevel.IPromptListener;
import prover.exec.toplevel.TopLevel;
import prover.exec.toplevel.exceptions.ProverException;
import prover.exec.toplevel.exceptions.SyntaxErrorException;



/**
 * The class CoqTop contains those higher level interactions with coq.
 * @author J. Charles
 */

public class BasicCoqTop extends TopLevel implements ITopLevel, IPromptListener {
	private LinkedList sections = new LinkedList();
	private LinkedList lemmas = new LinkedList();


	/**
	 * The simple constructor.
	 * @throws ProverException if it is unable to build the coq process.
	 */
	public BasicCoqTop (String [] strCoqTop) throws ProverException {
		super("Coq", strCoqTop, 100);
	}
	
	
	/**
	 * The one arg constructor.
	 * @param iGraceTime The grace time for TopLevel
	 * @throws ProverException if it is unable to build the coq process.
	 */
	public BasicCoqTop (String [] strCoqTop, int iGraceTime) throws ProverException {
		super("Coq", strCoqTop, iGraceTime);
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
	 * Abort the current proof.
	 * @throws ProverException if there is an unexpected problem
	 */
	public void abort() throws ProverException {
		sendCommand("Abort.");	
	}

	
	
	private int iStep;
	private int iProofStep;


	public boolean isProofMode() {
		return !getPrompt().startsWith("TopLevel <");
	}
	
	public int getStep() {
		return iStep;
	}
	public int getProofStep() {
		return iProofStep;
	}
	
	public void promptHasChanged(TopLevel caller) {
		String prompt = this.getPrompt();
		String [] tab = prompt.split("<");
		if(tab.length > 1) {
			String [] nums = tab[1].split("\\|");
			iStep = Integer.valueOf(nums[0].trim()).intValue();
			iProofStep = Integer.valueOf(nums[nums.length - 1].trim()).intValue();
		}		
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
	
}
