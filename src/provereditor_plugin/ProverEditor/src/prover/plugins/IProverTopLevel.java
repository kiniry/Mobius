package prover.plugins;

import org.eclipse.jface.text.IDocument;

import prover.exec.AProverException;
import prover.exec.ITopLevel;


/**
 * This interface is used at the plugin level, when extending the
 * prover.editor extension point.
 * It is used to handle all the interactions with the top level
 * API. It is done to specify all the prover specific behaviours.
 */
public interface IProverTopLevel {
	
	
	/** 
	 * the constant returned by 
	 * {@link #hasToSend(ITopLevel, IDocument, String, int, int)} or 
	 * {@link #hasToSend(ITopLevel, IDocument, String, int, int)}
	 * if the command shall be sent
	 * */ 
	public final int DONT_SKIP = 0;
	/** 
	 * the constant returned by 
	 * {@link #hasToSend(ITopLevel, IDocument, String, int, int)} or 
	 * {@link #hasToSend(ITopLevel, IDocument, String, int, int)}
	 * if the command shall be skipped and the evaluation shall
	 * end here
	 * */ 
	public final int SKIP = 1;
	/** 
	 * the constant returned by 
	 * {@link #hasToSend(ITopLevel, IDocument, String, int, int)} or 
	 * {@link #hasToSend(ITopLevel, IDocument, String, int, int)}
	 * if the command has to be skipped and the next command shall be
	 * evaluated
	 * */ 
	public final int SKIP_AND_CONTINUE = 2;

	/**
	 * Called when a command has to be send to the top level.
	 * @param itl The top level to whom the command shall be sent
	 * @param cmd The command to send
	 * @throws AProverException if there is an error while interacting with the top level
	 */
	public void sendCommand(ITopLevel itl, String cmd) throws AProverException;

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
	 * @return One of the values {@link prover.plugins.IProverTopLevel#DONT_SKIP} {@link prover.plugins.IProverTopLevel#SKIP} 
	 * 			or {@link prover.plugins.IProverTopLevel#SKIP_AND_CONTINUE}
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
	 * {@link prover.plugins.IProverTopLevel#SKIP_AND_CONTINUE} that could have happened
	 * @param end the ending point of the command in the text
	 * @return One of the values {@link prover.plugins.IProverTopLevel#DONT_SKIP} {@link prover.plugins.IProverTopLevel#SKIP} 
	 * 			or {@link prover.plugins.IProverTopLevel#SKIP_AND_CONTINUE}
	 */
	public int hasToSend(ITopLevel itl, IDocument doc, String cmd, int beg, int end);
	
	/**
	 * Sends to the top level the command to undo one step
	 * in the proof.
	 * @param itl The toplevel to send the command to
	 * @throws AProverException If anything goes wrong.
	 */
	public void undo(ITopLevel itl) throws AProverException;

	/**
	 * Compute the top-level command for a specific prover from the top-level path
	 * and the path to its libraries.
	 * @param top the toplevel path to the prover executable or wrapper shell script, as 
   * specified by the user in the preference page.
	 * @param path a sequence of fully resolved paths, the first element of which is where the
   * prover should run, and the other paths are library paths from the environment.  Your
   * prover may choose to ignore the running location specified in path[0] as Coq does.
	 * @return an array containing the command-line to execute the prover given this specificiation 
	 * as specified for {@link java.lang.Runtime#exec(java.lang.String[])}
	 */
  //@ example In the Coq plugin, top is (usually) "/usr/bin/coqtop" and path is an array with
  //          two elements, path[0] being "/home/foo/workspace/MyProject/" and path[1] is 
  //          "/home/foo/workspace/MyProject/some/path".  So Coq will run in path path[0] 
  //          but will look for theories in path[0] and path[1].  The result would be the
  //          array \result = { "/usr/bin/coqtop", "-I", path[0], "-I", path[1] }
	public String[] getCommands(String top, /*@ non_null @*/ String[] path);
}
