package mobius.prover.simplify;

import org.eclipse.jface.text.IDocument;

import mobius.prover.exec.AProverException;
import mobius.prover.exec.ITopLevel;
import mobius.prover.plugins.IProverTopLevel;

public class TopLevel implements IProverTopLevel {

  public String[] getCommands(String top, String[] path) {
    return new String [] {top};
  }

  public int hasToSkipSendCommand(ITopLevel itl, IDocument doc, String cmd,
                                  int beg, int end) {
    return DONT_SKIP;
  }

  public int hasToSkipUndo(ITopLevel itl, IDocument doc, String cmd, int beg,
                           int end) {
    return DONT_SKIP; // no undo actually
  }

  public void sendCommand(ITopLevel itl, String cmd) throws AProverException {
    System.out.println(cmd);
    itl.sendToProver(cmd);
  }

  public void undo(ITopLevel itl) throws AProverException {
    // nothing
    
  }

}
