package mobius.prover.cvc3;

import org.eclipse.jface.text.IDocument;

import mobius.prover.exec.AProverException;
import mobius.prover.exec.ITopLevel;
import mobius.prover.plugins.IProverTopLevel;
import mobius.prover.plugins.exceptions.SyntaxErrorException;

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
    int idx = cmd.lastIndexOf('(');

    if (idx != -1) {
      String mainCmd = cmd.substring(idx).trim();
      if (mainCmd.equals("(PROMPT_OFF)")) {
        return;
      }
    }
    //System.out.println(cmd);
    itl.sendToProver(cmd);
    String res = itl.getStdBuffer().trim();
    int tryout = 20; // we try 2 times
    while (!res.endsWith(">") && tryout > 0) {
      itl.waitForStandardInput();
      res += itl.getStdBuffer().trim();
      tryout --;
    }

    
    //System.out.println(res + itl.getErrBuffer().trim());
    res = res.substring(0, res.length() - 1);    
    res = res.trim();
    if (isErrorMsg(res)) {
      throw new SyntaxErrorException(res);
    }
  }

  public void undo(ITopLevel itl) throws AProverException {
    // nothing
    
  }

  public static boolean isErrorMsg(String s) {
    return s.startsWith("Bad input:") || s.trim().endsWith("Invalid.");
  }
}
