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
	
	public void waitForStandardInput() throws AProverException;
	public void waitForErrorInput() throws AProverException;
	
	public void addStandardStreamListener(IStreamListener isl);
	public void removeStandardStreamListener(IStreamListener isl);

	public void addErrorStreamListener(IStreamListener isl);
	public void removeErrorStreamListener(IStreamListener isl);


}
