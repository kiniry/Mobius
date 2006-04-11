package prover.plugins;

import org.eclipse.jface.text.IDocument;

import prover.exec.AProverException;
import prover.exec.ITopLevel;

public interface IProverTopLevel {
	
	
	public void sendCommand(ITopLevel itl, String s) throws AProverException;

	/**
	 * Called before sending an {@link prover.exec.toplevel.TopLevel#undo()} command to the 
	 * top level when in a file context.
	 * Used to determine wether the we shall send  {@link prover.exec.toplevel.TopLevel#undo()}
	 * to the top level, we shall skip it and stop or
	 * {@link prover.exec.toplevel.TopLevel#undo()} for the preceding part of the document.
	 * @param doc The current document from which the command was taken
	 * @param cmd The command that will be sent
	 * @param beg the starting point of the command in the text
	 * @param end the ending point of the command in the text
	 * @return One of the values {@link prover.exec.ITopLevel#DONT_SKIP} {@link prover.exec.ITopLevel#SKIP} 
	 * 			or {@link prover.exec.ITopLevel#SKIP_AND_CONTINUE}
	 */
	public int hasToSkip(ITopLevel itl, IDocument doc, String cmd, int beg, int end);
	
	
	/**
	 * Called before sending a command through {@link prover.exec.toplevel.TopLevel#sendCommand(String)} to
	 * the top level.
	 * Used to determine wether the next command should be
	 * sent to the top level, we shall skip it and stop or
	 * we shall skip it and try to evaluate the next command. 
	 * @param doc The current document from which the command was taken
	 * @param cmd The command that will be sent
	 * @param beg the command in the text before any 
	 * {@link prover.exec.ITopLevel#SKIP_AND_CONTINUE} that could have happened
	 * @param end the ending point of the command in the text
	 * @return One of the values {@link prover.exec.ITopLevel#DONT_SKIP} {@link prover.exec.ITopLevel#SKIP} 
	 * 			or {@link prover.exec.ITopLevel#SKIP_AND_CONTINUE}
	 */
	public int hasToSend(ITopLevel itl, IDocument doc, String cmd, int beg, int end);
	
	/**
	 * Sends to the top level the command to undo one step
	 * in the proof.
	 * @param itl The toplevel to send the command to
	 * @throws AProverException If anything goes wrong.
	 */
	public void undo(ITopLevel itl) throws AProverException;

	public String[] getCommands(String top, String[] path);
}
