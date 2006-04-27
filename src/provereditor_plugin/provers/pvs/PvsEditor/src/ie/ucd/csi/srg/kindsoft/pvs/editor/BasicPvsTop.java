package ie.ucd.csi.srg.kindsoft.pvs.editor;

import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.graphics.Resource;
import org.eclipse.ui.PlatformUI;

import prover.exec.AProverException;
import prover.exec.ITopLevel;
import prover.plugins.IProverTopLevel;

/**
 * Top-level interactions with PVS.
 *
 * @author Joe Kiniry (kiniry@ucd.ie)
 * @version 26 April 2006
 */
// @explanation 
// @module 
// @organisation School of Computer Science and Informatics
// @copyright University College Dublin

public class BasicPvsTop implements IProverTopLevel {
  
  // review jgc Find the method call to get the root path of the current workspace.
  // review jgc, jrk Perhaps change this into a ResourceBundle?
  private String my_context_path = Platform.getInstanceLocation().toString();

  public void sendCommand(ITopLevel itl, String cmd) throws AProverException {
    //@ assert false;
    // todo Implement this method.
    assert false : "This method is not yet implemented.";
    return;
  }

  public int hasToSkip(ITopLevel itl, IDocument doc, String cmd, int beg, int end) {
    //@ assert false;
    // todo Implement this method.
    assert false : "This method is not yet implemented.";
    return 0;
  }

  public int hasToSend(ITopLevel itl, IDocument doc, String cmd, int beg, int end) {
    //@ assert false;
    // todo Implement this method.
    assert false : "This method is not yet implemented.";
    return 0;
  }

  public void undo(ITopLevel itl) throws AProverException {
    //@ assert false;
    // todo Implement this method.
    assert false : "This method is not yet implemented.";
    return;
  }

  public String[] getCommands(String top, String[] path) {
    String[] result = { top, "-raw", "-nobg" };
    if (path[0] != null)
      my_context_path = path[0];
    return result;
  }

}
