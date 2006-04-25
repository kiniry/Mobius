/*
 * Created on Mar 3, 2005
 */
package fr.inria.everest.coq.editor;

import java.util.LinkedList;
import java.util.Stack;

import org.eclipse.jface.text.IDocument;

import fr.inria.everest.coq.editor.utils.Proof;

import prover.exec.AProverException;
import prover.exec.ITopLevel;
import prover.plugins.IProverTopLevel;
import prover.plugins.exceptions.ProverException;
import prover.plugins.exceptions.SyntaxErrorException;



/**
 * The class BasicCoqTop contains minimal higher level interactions with the toplevel.
 * @author J. Charles
 */

public class BasicCoqTop implements IProverTopLevel  {
	private LinkedList proofList = new LinkedList();
	private int fLast;
	private Proof fCurrentProof;
	private Stack fProofs = new Stack();
	
	public boolean isProofMode(ITopLevel itl) {
		try {
			while(itl.getErrBuffer().trim().equals("") && itl.isAlive())
				itl.waitForErrorInput();
		} catch (AProverException e) {}
		return !itl.getErrBuffer().trim().startsWith("Coq <");
	}	
	
	/**
	 * Send the given command to coqtop. A command is a sentence which ends with a dot.
	 * @param s The command to send
	 * @throws SyntaxErrorException If coq yells about a syntax error.
	 * @throws ProverException if there is an unexpected problem
	 */
	public void sendCommand(ITopLevel itl, String s) throws AProverException {
//		System.out.println(s);
		itl.sendToProver(s);
	
		while(itl.getErrBuffer().trim().equals("") && itl.isAlive())
			itl.waitForErrorInput();
		if(itl.getStdBuffer().trim().equals(""))
			itl.waitForStandardInput();
		String str = itl.getStdBuffer().trim();
		//System.out.println(str);
		if(str.indexOf("Syntax error: ") != -1)
			throw new SyntaxErrorException(str.toString());
		if(str.indexOf("Error:") != -1)
			throw new SyntaxErrorException(str.toString());
		if(str.indexOf("Anomaly:") != -1)
			throw new SyntaxErrorException(str.toString());
		if(str.startsWith("Toplevel input") || str.indexOf("User error") != -1)
			throw new ProverException("An error occured during the proof:\n" + str + "\n");
	}
	
	
	
	/*
	 *  (non-Javadoc)
	 * @see prover.plugins.IProverTopLevel#undo(prover.exec.ITopLevel)
	 */
	public void undo(ITopLevel itl) throws AProverException {
		if(isProofMode(itl)) {
			try {
				sendCommand(itl, "Undo 1.");
			}
			catch (Exception e) {
				sendCommand(itl, "Abort.");
			}
		}
		else {
			sendCommand(itl, "Back 1.");
		}
	}	
	

	/*
	 *  (non-Javadoc)
	 * @see prover.plugins.IProverTopLevel#hasToSkip(prover.exec.ITopLevel, org.eclipse.jface.text.IDocument, java.lang.String, int, int)
	 */
	public int hasToSkip(ITopLevel itl, IDocument document, String cmd, int beg, int end) {
		if(fCurrentProof != null) {
			// we might be within a proof
			if(!isProofMode(itl)) {
				// we are at the end of a proof
				if(fCurrentProof.fNamePos != beg)
					return IProverTopLevel.SKIP_AND_CONTINUE;
				else {
					fCurrentProof = null;
					return IProverTopLevel.DONT_SKIP;
				}
			}
			else  {
				if(cmd.startsWith("Proof"))
					return IProverTopLevel.SKIP;
				return IProverTopLevel.DONT_SKIP;
			}
		}
		else {
			// we are outside the proof or at the begining of one
			Proof p = (Proof)fProofs.peek();
			if(p.isWithinProof(beg)) {
				if(p.fNamePos == beg) {
					fProofs.pop();
					return IProverTopLevel.DONT_SKIP;
				}
				return IProverTopLevel.SKIP_AND_CONTINUE;
			}
				
			
		}
		if((cmd.startsWith("Show ")) ||
			(cmd.startsWith("Print ")))
			return IProverTopLevel.SKIP;
		return IProverTopLevel.DONT_SKIP;
	}

	
	/*
	 *  (non-Javadoc)
	 * @see prover.plugins.IProverTopLevel#hasToSend(prover.exec.ITopLevel, org.eclipse.jface.text.IDocument, java.lang.String, int, int)
	 */
	public int hasToSend(ITopLevel itl, IDocument doc, String cmd, int beg, int end) {		
		if(isProofMode(itl)) {
			if (fCurrentProof == null) {
				proofList.addFirst(itl.getErrBuffer().split(" ")[0]);
				fCurrentProof = new Proof();
				fCurrentProof.fBeginPos = beg;
				fCurrentProof.fNamePos = fLast;
				System.err.println(fCurrentProof.getProof(doc));
			}
			else {
				if (!(itl.getErrBuffer().startsWith(proofList.getFirst().toString()))) {
					proofList.addFirst(itl.getErrBuffer().split(" ")[0]);
					fCurrentProof.fEndPos = beg;
					fProofs.push(fCurrentProof);
					fCurrentProof = null;
				}
			}
		}
		else if((!isProofMode(itl)) && (fCurrentProof != null)) {
			fCurrentProof.fEndPos = beg;
			fProofs.push(fCurrentProof);
			fCurrentProof = null;
			
		}
		fLast = beg;
		return IProverTopLevel.DONT_SKIP;

	}
	
	
	
	/*
	 *  (non-Javadoc)
	 * @see prover.plugins.IProverTopLevel#getCommands(java.lang.String, java.lang.String[])
	 */
	public String[] getCommands(String top, String[] path) {
		String [] cmds;
		if(path != null) {
			cmds = new String[1 + path.length * 2];
			for(int i = 0; i < path.length; i++) {
				cmds[(2 * i) + 1] = "-I";
				cmds[(2 * i) + 2] = path[i];
			}
			
		}
		else {
			cmds = new String[1];
		}
		cmds[0] = top;
		//cmds[cmds.length - 1] = "-emacs";
		return cmds;
	}
}
