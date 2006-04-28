package ie.ucd.csi.srg.kindsoft.pvs.editor;

import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.graphics.Resource;
import org.eclipse.ui.PlatformUI;

import prover.exec.AProverException;
import prover.exec.ITopLevel;
import prover.plugins.IProverTopLevel;
import prover.plugins.exceptions.ProverException;
import prover.plugins.exceptions.SyntaxErrorException;

/**
 * Top-level interactions with PVS.
 *
 * @author Joe Kiniry (kiniry@ucd.ie)
 * @version 26 April 2006
 */
// @explanation Top-level interactions with PVS.
// @module MOBIUS.PROOF_EDITOR.PVS.EDITOR
// @organisation School of Computer Science and Informatics
// @copyright University College Dublin

public class BasicPvsTop implements IProverTopLevel {
  
  // @review jgc Find the method call to get the root path of the current workspace.
  // @review jgc, jrk Perhaps change this into a ResourceBundle?
  private String my_context_path = Platform.getInstanceLocation().toString();

  public void sendCommand(ITopLevel itl, String cmd) throws AProverException {
    // Send the command to the prover.  Note that we do no analysis of the command here at 
    // all.
    itl.sendToProver(cmd);
    // Wait for a response of some kind from PVS via its error and standard output.
    while(itl.getErrBuffer().trim().equals("") && itl.isAlive())
      itl.waitForErrorInput();
    if(itl.getStdBuffer().trim().equals(""))
      itl.waitForStandardInput();
    /// Get the standard output response.
    String prover_response = itl.getStdBuffer().trim();
    
    if(prover_response.indexOf(":pvs-err") != -1)
      throw new PvsProverException(prover_response.toString());
    if(prover_response.indexOf(":pvs-warn") != -1)
      throw new PvsProverException(prover_response.toString());
    // @todo jrk Deal with all of the output types specified in pvs-ilisp.el:pvs-output-filter.
  }

  public int hasToSkipUndo(ITopLevel itl, IDocument doc, String cmd, int beg, int end) {
    //@ assert false;
    // @todo Implement this method.
    assert false : "This method is not yet implemented.";
    return 0;
  }

  public int hasToSkipSendCommand(ITopLevel itl, IDocument doc, String cmd, int beg, int end) {
    //@ assert false;
    // @todo Implement this method.
    assert false : "This method is not yet implemented.";
    return 0;
  }

  public void undo(ITopLevel itl) throws AProverException {
    sendCommand(itl, "(undo 1)");
  }

  public String[] getCommands(String top, String[] path) {
    String[] result = { top, "-raw", "-nobg" };
    if (path[0] != null)
      my_context_path = path[0];
    return result;
  }

}
