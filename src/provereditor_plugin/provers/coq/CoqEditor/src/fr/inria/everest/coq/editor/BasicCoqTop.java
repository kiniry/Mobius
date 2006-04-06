/*
 * Created on Mar 3, 2005
 */
package fr.inria.everest.coq.editor;

import org.eclipse.jface.text.IDocument;

import prover.exec.AProverException;
import prover.exec.ITopLevel;
import prover.exec.toplevel.IPromptListener;
import prover.exec.toplevel.TopLevel;
import prover.exec.toplevel.exceptions.ProverException;
import prover.exec.toplevel.exceptions.SyntaxErrorException;



/**
 * The class BasicCoqTop contains minimal higher level interactions with the toplevel.
 * @author J. Charles
 */

public class BasicCoqTop extends TopLevel implements ITopLevel, IPromptListener {


	/**
	 * The simple constructor.
	 * @throws ProverException if it is unable to build the coq process.
	 */
	public BasicCoqTop (String [] strCoqTop) throws ProverException {
		this(strCoqTop, 100);
	}
	
	
	/**
	 * The one arg constructor.
	 * @param iGraceTime The grace time for TopLevel
	 * @throws ProverException if it is unable to build the coq process.
	 */
	public BasicCoqTop (String [] strCoqTop, int iGraceTime) throws ProverException {
		super("Coq", strCoqTop, iGraceTime);
		this.addPromptListener(this);
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


	public int hasToSkip(IDocument document, String cmd, int beg, int end) {
		if(cmd.startsWith("Proof"))
			return SKIP;
		return DONT_SKIP;
	}


	public int hasToSend(IDocument doc, String cmd, int beg, int end) {
		return DONT_SKIP;
	}


	public void undo() throws AProverException {
		undo(1);
	}
	
}
