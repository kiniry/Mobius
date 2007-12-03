package mobius.prover.plugins;

import mobius.prover.exec.AProverException;
import mobius.prover.exec.ITopLevel;

import org.eclipse.jface.text.IDocument;



/**
 * This interface is used at the plugin level, when extending the
 * prover.editor extension point.
 * It is used to handle all the interactions with the top level
 * API. It is done to specify all the prover specific behaviours.
 */
public interface IProverTopLevel {
  
  /** 
   * The constant returned by 
   * {@link #hasToSkipSendCommand(ITopLevel, IDocument, String, int, int)} or 
   * {@link #hasToSkipSendCommand(ITopLevel, IDocument, String, int, int)}
   * that denotes the command in question should/will be sent to the prover.
   */ 
  public final static int DONT_SKIP = 0;
  
  /** 
   * The constant returned by 
   * {@link #hasToSkipSendCommand(ITopLevel, IDocument, String, int, int)} or 
   * {@link #hasToSkipSendCommand(ITopLevel, IDocument, String, int, int)}
   * that denotes the command in question should/will be skipped and the evaluation will
   * end immediately.
   */ 
  public final static int SKIP = 1;
  
  /** 
   * The constant returned by 
   * {@link #hasToSkipSendCommand(ITopLevel, IDocument, String, int, int)} or 
   * {@link #hasToSkipSendCommand(ITopLevel, IDocument, String, int, int)}
   * that denotes the command in question should/will be skipped and the next command will be
   * evaluated.
   */ 
  public final static int SKIP_AND_CONTINUE = 2;

  /**
   * Send the string <var>cmd</var> to the top-level of the theorem prover available via 
   * <var>itl</var>.
   *
   * @param itl the top-level to whom the command shall be sent.
   * @param cmd the command to send.
   * @throws AProverException indicates that an error occured while interacting with the 
   * prover top-level.
   */
  public void sendCommand(/*@ non_null @*/ ITopLevel itl, /*@ non_null @*/ String cmd)
    throws AProverException;

  /**
   * This method is always called before {@link mobius.prover.exec.toplevel.TopLevel#undo()} is 
   * called if the undo action was triggered by the GUI.
   *
   * <p> This method must determine whether:
   * <ul>
   * <li> send the undo command while in {@link TopLevel#undo()} to the top-level, </li>
   * <li> skip the undo command and stop, and therefore do not send it while in 
   * {@link #undo(ITopLevel)} method, or </li>
   * <li> skip this particular undo command and attempt to undo again. </li>
   * <ul>
   * </p>
   * 
   * <p> For example, consider the following Coq (bracketed numbers on the right are not Coq
   * syntax but are just used for expository purpose):
   * <pre>
   * Qed.                    [-3]
   *                         [-2]
   * 
   *                         [0]
   * Lemma l :True.          [1]
   * Proof.                  [2]
   * idtac.                  [3]
   * exact I.                [4]
   * Print I.                [5]
   * Qed.                    [6]
   *                         [7]
   * </pre>
   * 
   * <p> Undo actions will have the following effect:
   * <pre>
   * initial state    final state
   * [7]              [0] and Lemma l is undefined by using the "back" command.
   * [6]              [5] so that the user can reexecute the Print command if they desire
   *                  but no command was sent to the prover at all as this particular step/
   *                  construct is just a visual update.
   * [5]              [4] and a true "undo" command is sent to undo the exact tactic.
   * [4]              [3] and a true "undo" command is sent to undo the idtac tactic.
   * [3]              [2] but no command was sent to the prover at all.  This is a special
   *                  case in Coq because the Proof statement can modify the theory/proof
   *                  state in Coq.
   * [2]              [-2] and an "abort" command is sent to the prover to abort the definition
   *                  of Lemma l.
   * </pre>
   * </p>
   *
   * @param itl the top-level to whom the command shall be sent.
   * @param doc the current document from which the command was taken.
   * @param cmd the command that will be sent to the next {@link #undo(ITopLevel)} call.
   * @param beg the starting point of the command in the text.
   * @param end the ending point of the command in the text.
   * @return One of the values {@link mobius.prover.plugins.IProverTopLevel#DONT_SKIP},
   * {@link mobius.prover.plugins.IProverTopLevel#SKIP}, or 
   * {@link mobius.prover.plugins.IProverTopLevel#SKIP_AND_CONTINUE}
   */
  /*@ requires 0 <= beg & beg <= end;
    @ ensures \result == IProverTopLevel.DONT_SKIP | 
    @                    IProverTopLevel.SKIP | 
    @                    IProverTopLevel.SKIP_AND_CONTINUE;
    @*/
  public int hasToSkipUndo(/*@ non_null @*/ ITopLevel itl, /*@ non_null @*/ IDocument doc, 
                           /*@ non_null @*/ String cmd, int beg, int end);
  
  /**
   * Like the {@link #hasToSkipUndo(ITopLevel, IDocument, String, int, int)} command, this 
   * method is always called before the {@link #sendCommand(ITopLevel, String)} method is 
   * called.
   * 
   * <p> This method must determine whether:
   * <ul>
   * <li> send the command while in {@link #sendCommand(ITopLevel, String)()} to the 
   * top-level, </li>
   * <li> skip the command command and stop, and therefore do not send it while in 
   * {@link #sendCommand(ITopLevel, String)} method, or </li>
   * <li> skip this particular send command and attempt to send again (i.e., evaluate the
   * next command). </li>
   * <ul>
   * </p>
   * 
   * @param itl the top-level to whom the command shall be sent.
   * @param doc the current document from which the command was taken.
   * @param cmd the command that will be sent to the next {@link #undo(ITopLevel)} call.
   * @param beg the command in the text before any 
   * {@link mobius.prover.plugins.IProverTopLevel#SKIP_AND_CONTINUE} that could have happened.
   * @param end the ending point of the command in the text.
   * @return One of the values {@link mobius.prover.plugins.IProverTopLevel#DONT_SKIP},
   * {@link mobius.prover.plugins.IProverTopLevel#SKIP}, or 
   * {@link mobius.prover.plugins.IProverTopLevel#SKIP_AND_CONTINUE}
   */
  // @todo Review the meaning of "doc", "beg", and "end" in this method and its peer above.
  public int hasToSkipSendCommand(ITopLevel itl, IDocument doc, String cmd, int beg, int end);
  
  /**
   * Send the appropriate "undo" command to the top-level of the theorem prover available via
   * <var>itl</var>.  This method is used generically and only should undo one step.
   * E.g., in PVS and Coq one can undo a single proof step; whereas in Coq one can also
   * undo a single command like a type, axiom, formula, etc. declaration/definition.
   *
   * @param itl the top-level to whom the command shall be sent.
   * @throws AProverException indicates that an error occured while interacting with the 
   * prover top-level.
   */
  public void undo(/*@ non_null @*/ ITopLevel itl) throws AProverException;

  /**
   * Compute the top-level command for a specific prover from the top-level path
   * and the path to its libraries.
   * 
   * @param top the toplevel path to the prover executable or wrapper shell script, as 
   * specified by the user in the preference page.
   * @param path a sequence of fully resolved paths, the first element of which is where the
   * prover should run, and the other paths are library paths from the environment.  Your
   * prover may choose to ignore the running location specified in path[0] as Coq does.
   * @return an array containing the command-line to execute the prover given this 
   * specificiation as specified for {@link java.lang.Runtime#exec(java.lang.String[])}
   */
  // @example In the Coq plugin, top is (usually) "/usr/bin/coqtop" and path is
  // an array with two elements, path[0] being "/home/foo/workspace/MyProject/"
  // and path[1] is "/home/foo/workspace/MyProject/some/path". So Coq will run
  // in path path[0] but will look for theories in path[0] and path[1]. The
  // result would be the array \result = { "/usr/bin/coqtop", "-I", path[0],
  // "-I", path[1] }
  public /*@ non_null @*/ String[] getCommands(/*@ non_null @*/ String top,
                                               /*@ non_null @*/ String[] path);

}
