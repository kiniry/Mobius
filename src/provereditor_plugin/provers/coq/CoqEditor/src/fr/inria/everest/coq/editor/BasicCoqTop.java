/*
 * Created on Mar 3, 2005
 */
package fr.inria.everest.coq.editor;

import java.util.LinkedList;
import java.util.Stack;

import org.eclipse.jface.text.IDocument;

import prover.exec.AProverException;
import prover.exec.ITopLevel;
import prover.exec.toplevel.TopLevel;
import prover.exec.toplevel.exceptions.ProverException;
import prover.exec.toplevel.exceptions.SyntaxErrorException;



/**
 * The class BasicCoqTop contains minimal higher level interactions with the toplevel.
 * @author J. Charles
 */

public class BasicCoqTop extends TopLevel implements ITopLevel {


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
	
	public void undo() throws AProverException {
		if(isProofMode()) {
			try {
				sendCommand("Undo 1.");
			}
			catch (Exception e) {
				sendCommand("Abort.");
			}
		}
		else
			sendCommand("Back 1.");
	}	
	

	public boolean isProofMode() {
		return !getPrompt().startsWith("Coq <");
	}
	




	Stack proofBeginList = new Stack();
	Stack proofEndList = new Stack();
	
	public int hasToSkip(IDocument document, String cmd, int beg, int end) {
		if(proofBeginList.size() > 0) {
			if((isProofMode())) {
				if(proofBeginList.size() == proofEndList.size()) {
					proofEndList.pop();
					return SKIP_AND_CONTINUE;
				}
				if(cmd.startsWith("Proof"))
					return SKIP;
			}
			else {
				int begProof = ((Integer) proofBeginList.peek()).intValue();
				if(proofBeginList.size() == proofEndList.size()) {
					//we can be outside a proof
					int endProof = ((Integer) proofEndList.peek()).intValue();

					if (endProof == beg) {
						// we are in fact inside a the end of the proof
						proofEndList.pop();
						
//						if(begProof == beg) {
//							proofBeginList.removeFirst();
//						}
						return DONT_SKIP;
					}
				}
				else {
					if(begProof == beg) {
						// we are outside a proof
						proofBeginList.pop();
						return SKIP_AND_CONTINUE;
					}
					else {
						// we are within a proof
						return SKIP_AND_CONTINUE;
					}
				}
			}
		}
		return DONT_SKIP;
	}

	LinkedList proofList = new LinkedList();
	public int hasToSend(IDocument doc, String cmd, int beg, int end) {
		
		if(isProofMode()) {
			if (proofBeginList.size() == proofEndList.size()) {
				proofBeginList.push(new Integer(beg));
				proofList.addFirst(getPrompt().split(" ")[0]);
			}
			else {
				if (!(getPrompt().startsWith(proofList.getFirst().toString()))) {
					proofEndList.push(new Integer(beg));
					proofBeginList.push(new Integer(beg));
					proofList.addFirst(getPrompt().split(" ")[0]);
				}
			}
		}
		else if((!isProofMode()) && (proofBeginList.size() != proofEndList.size())) {
			proofEndList.push(new Integer(beg));

		}
		return DONT_SKIP;
	}


	
}
