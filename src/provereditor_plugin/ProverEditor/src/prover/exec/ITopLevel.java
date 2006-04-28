package prover.exec;

import prover.exec.toplevel.stream.IStreamListener;

/**
 * Basic interactions needed to dialog with the toplevel.
 * @author J.Charles
 *
 */
public interface ITopLevel {
	
	/**
	 * Sends a command to the top level. Any pre treatment
	 * regarding the command to send to the prover should be
	 * done before this call.
	 * @param s The command to send to the prover.
	 * @throws AProverException thrown if anything goes wrong.
	 */
  //@ signals (TopLevelDeathException) !isAlive(); 
	public void sendToProver(String s) throws AProverException;
	
	
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
	 * Clear the snapshot of the standard output
	 * and the error output of the prover.
	 */
	public void clearBuffer();
	
	/**
	 * Clear the snapshot of the standard output of the prover.
	 */
	public void clearStdBuffer();
	
	/**
	 * Clear the snapshot of the error output of the prover.
	 */
	public void clearErrBuffer();
	
	
	/**
	 * Returns the content of the standard output from the prover.
	 * @return A snapshot of the standard output of the prover
	 */
	public String getStdBuffer();

	/**
	 * Returns the content of the error output from the prover.
	 * @return A snapshot of the error output of the prover
	 */
	public String getErrBuffer();
	
	/**
	 * Wait for the input coming from the standard stream.
	 * It fills the internal buffer with the informations.
	 * @throws AProverException In case of the grace time, 
	 * death of the thread, death of the prover, or an I/O error
	 */
	public void waitForStandardInput() throws AProverException;
	
	/**
	 * Wait for the input coming from the error stream.
	 * It fills the internal buffer with the informations.
	 * @throws AProverException In case of the grace time, 
	 * death of the thread, death of the prover, or an I/O error
	 */
	public void waitForErrorInput() throws AProverException;
	
	/**
	 * Add a listener to listen to the events of the standard stream.
	 * @param isl the listener to add
	 */
	public void addStandardStreamListener(IStreamListener isl);
	
	/**
	 * Remove a listener that was previously registered to listen
	 * to the standard stream
	 * @param isl the listener to remove
	 */
	public void removeStandardStreamListener(IStreamListener isl);

	/**
	 * Add a listener to listen to the events of the error stream.
	 * @param isl the listener to add
	 */
	public void addErrorStreamListener(IStreamListener isl);

	/**
	 * Remove a listener that was previously registered to listen
	 * to the error stream
	 * @param isl the listener to remove
	 */
	public void removeErrorStreamListener(IStreamListener isl);


}
