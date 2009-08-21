package mobius.prover.simplify;

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
    String mainCmd = cmd.substring(cmd.lastIndexOf('(')).trim();
    if (!mainCmd.equals("(PROMPT_OFF)")) {
      itl.sendToProver(cmd);
    }
    String res = itl.getStdBuffer().trim();
    if (isErrorMsg(itl.getStdBuffer().trim())) {
      if (res.endsWith(">")) {
        res = res.substring(0, res.length() - 1);
      }
      throw new SyntaxErrorException(res);
    }
  }

  public void undo(ITopLevel itl) throws AProverException {
    // nothing
    
  }

  public static boolean isErrorMsg(String s) {
    System.out.println(s);
    return s.startsWith("Bad input:");
  }
}
