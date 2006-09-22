/*
 * Created on Mar 3, 2005
 */
package fr.inria.everest.coq.editor;

import org.eclipse.jface.text.IDocument;

import prover.exec.AProverException;
import prover.exec.ITopLevel;
import prover.plugins.IProverTopLevel;
import prover.plugins.exceptions.ProverException;
import prover.plugins.exceptions.SyntaxErrorException;
import fr.inria.everest.coq.editor.utils.ProofHandler;



/**
 * The class BasicCoqTop contains minimal higher level interactions with the toplevel.
 * @author J. Charles
 */

public class BasicCoqTop implements IProverTopLevel  {

	/** if fModuleName <> <code>null</code> we are trying to skip a module */ 
	private String fModuleName = null;
	/** object to help skip proofs */
	private ProofHandler ph = new ProofHandler();
	
	
	/**
	 * Tell whether or not we are doing a proof.
	 * ie. if the prompt begins by something else than 'Coq'.
	 * @param itl the current top level to consider
	 * @return <code>true</code> or <code>false</code> depending if we are within a proof
	 */
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
		try {
			itl.sendToProver(s);
		}
		catch (AProverException e){
			e.printStackTrace();
			throw e;
		}
		while(itl.getErrBuffer().trim().equals("") && itl.isAlive())
			itl.waitForErrorInput();
		if(itl.getStdBuffer().trim().equals(""))
			itl.waitForStandardInput();
		String str = itl.getStdBuffer().trim();
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
	public int hasToSkipUndo(ITopLevel itl, IDocument document, String cmd, int beg, int end) {

		int res;
		if((res = ph.hasToSkip(this, itl, document, cmd, beg, end)) 
				!= IProverTopLevel.DONT_SKIP) {
			return res;
		}
		if(fModuleName != null) {
			// fetch the end of a module
			if((cmd.indexOf("Module " + fModuleName) != -1) ||
				(cmd.indexOf("Module Type " + fModuleName) != -1) ||
				(cmd.indexOf("Section " + fModuleName) != -1)) {
				fModuleName = null;
				return IProverTopLevel.DONT_SKIP;
			}
			return IProverTopLevel.SKIP_AND_CONTINUE;
		}
		if(cmd.trim().startsWith("End ")) {
			// we will have to skip a module :)
			fModuleName = cmd.substring(4, cmd.length() - 1);
			return IProverTopLevel.SKIP_AND_CONTINUE;
		}
		
		// the commands to skip
		String [] vernac = {"Proof", "Show ", "Print "};
		for (int i = 0; i < vernac.length; i++) {
			if(cmd.startsWith(vernac[i])) {
				return IProverTopLevel.SKIP;
			}
		}
		
		// in doubt we evaluate
		return IProverTopLevel.DONT_SKIP;
	}

	
	/*
	 *  (non-Javadoc)
	 * @see prover.plugins.IProverTopLevel#hasToSend(prover.exec.ITopLevel, org.eclipse.jface.text.IDocument, java.lang.String, int, int)
	 */

	
	public int hasToSkipSendCommand(ITopLevel itl, IDocument doc, String cmd, int beg, int end) {
		int res;
		if((res = ph.hasToSend(this, itl, doc, cmd, beg, end)) 
				!= IProverTopLevel.DONT_SKIP) {
			return res;
		}
		return IProverTopLevel.DONT_SKIP;
	}
	
	/*
	 *  (non-Javadoc)
	 * @see prover.plugins.IProverTopLevel#getCommands(java.lang.String, java.lang.String[])
	 */
	public String[] getCommands(String top, String[] path) {
		String [] cmds;
		if(path != null) {
			cmds = new String[2 + path.length * 2];
			
			for(int i = 0; i < path.length; i++) {
				cmds[(2 * i) + 2] = "-I";
				cmds[(2 * i) + 3] = path[i];
			}
			
		}
		else {
			cmds = new String[2];
		}
		cmds[0] = top;
		cmds[1] = "-emacs";
		return cmds;
	}
}
