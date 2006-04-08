package prover.exec;

import org.eclipse.jface.text.IDocument;

import prover.exec.toplevel.stream.IStreamListener;

/**
 * Basic interactions needed to dialog with the toplevel.
 * @author J.Charles
 *
 */
public interface ITopLevel {
	public final int DONT_SKIP = 0;
	public final int SKIP = 1;
	public final int SKIP_AND_CONTINUE = 2;
	
	/**
	 * Sends a command to the top level. Any pre treatment
	 * regarding the command to send to the prover should be
	 * done here.
	 * @param cmd The command to send to the prover.
	 * @throws AProverException thrown if anything goes wrong.
	 */
	public void sendCommand(String s) throws AProverException;
	

	/**
	 * Sends to the top level the command to undo one step
	 * in the proof.
	 * @throws AProverException If anything goes wrong.
	 */
	public void undo() throws AProverException;
	
	/**
	 * If the user tells  the prover to stop what it is
	 * currently doing; usually by sending a Ctrl-Break 
	 * message or something like that.
	 * @throws AProverException
	 */
	public void doBreak() throws AProverException;
	
	
	/**
	 * Tells wether or not the top level is alive.
	 * @return true if the top level is working.
	 */
	public boolean isAlive();
	
	/**
	 * Stop the top level process.
	 */
	public void stop();
	
	/**
	 * Called before sending an {@link #undo()} command to the 
	 * top level when in a file context.
	 * Used to determine wether the we shall send  {@link #undo()}
	 * to the top level, we shall skip it and stop or
	 * {@link #undo()} for the preceding part of the document.
	 * @param doc The current document from which the command was taken
	 * @param cmd The command that will be sent
	 * @param beg the starting point of the command in the text
	 * @param end the ending point of the command in the text
	 * @return One of the values {@link #DONT_SKIP} {@link #SKIP} 
	 * 			or {@link #SKIP_AND_CONTINUE}
	 */
	public int hasToSkip(IDocument doc, String cmd, int beg, int end);
	
	
	/**
	 * Called before sending a command through {@link #sendCommand(String)} to
	 * the top level.
	 * Used to determine wether the next command should be
	 * sent to the top level, we shall skip it and stop or
	 * we shall skip it and try to evaluate the next command. 
	 * @param doc The current document from which the command was taken
	 * @param cmd The command that will be sent
	 * @param beg the command in the text before any 
	 * {@link #SKIP_AND_CONTINUE} that could have happened
	 * @param end the ending point of the command in the text
	 * @return One of the values {@link #DONT_SKIP} {@link #SKIP} 
	 * 			or {@link #SKIP_AND_CONTINUE}
	 */
	public int hasToSend(IDocument doc, String cmd, int beg, int end);
	
	
	
	public void clearBuffer();
	public String getStdBuffer();
	
	public void addStreamListener(IStreamListener isl);
	public void removeStreamListener(IStreamListener isl);

	public void addErrorStreamListener(IStreamListener isl);
	public void removeErrorStreamListener(IStreamListener isl);
	
}
