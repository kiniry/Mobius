/*
 * Created on Mar 3, 2005
 */
package fr.inria.everest.coq.editor;

import mobius.prover.exec.AProverException;
import mobius.prover.exec.ITopLevel;
import mobius.prover.plugins.IProverTopLevel;
import mobius.prover.plugins.exceptions.ProverException;
import mobius.prover.plugins.exceptions.SyntaxErrorException;

import org.eclipse.jface.text.IDocument;

import fr.inria.everest.coq.editor.utils.ProofHandler;



/**
 * The class BasicCoqTop contains minimal higher level interactions with the toplevel.
 * @author J. Charles
 */
public class BasicCoqTop implements IProverTopLevel  {

  /** if fModuleName <> <code>null</code> we are trying to skip a module. */ 
  private String fModuleName;
  /** object to help skip proofs. */
  private ProofHandler fProofHandler = new ProofHandler();
  
  
  /**
   * Tell whether or not we are doing a proof.
   * ie. if the prompt begins by something else than 'Coq'.
   * @param itl the current top level to consider
   * @return <code>true</code> or <code>false</code> depending if we are within a proof
   */
  public boolean isProofMode(final ITopLevel itl) {
    try {
      while (itl.getErrBuffer().trim().equals("") && itl.isAlive()) {
        itl.waitForErrorInput();
      }
    }
    catch (AProverException e) {
      
    }
    return !itl.getErrBuffer().trim().startsWith("Coq <");
  }  
  
  /**
   * Send the given command to coqtop. A command is a sentence which ends with a dot.
   * @param itl the current top level to consider
   * @param s The command to send
   * @throws SyntaxErrorException If coq yells about a syntax error.
   * @throws AProverException if there is an unexpected problem
   */
  public void sendCommand(final ITopLevel itl, 
                          final String s) 
    throws AProverException, SyntaxErrorException {
    try {
      itl.sendToProver(s);
    }
    catch (AProverException e) {
      e.printStackTrace();
      throw e;
    }
    while (itl.getErrBuffer().trim().equals("") && itl.isAlive()) {
      itl.waitForErrorInput();
    }
    if (itl.getStdBuffer().trim().equals("")) {
      itl.waitForStandardInput();
    }
    final String str = itl.getStdBuffer().trim();
    if (str.indexOf("Syntax error: ") != -1) {
      throw new SyntaxErrorException(str);
    }
    if (str.indexOf("Error:") != -1) {
      throw new SyntaxErrorException(str);
    }
    if (str.indexOf("Anomaly:") != -1) {
      throw new SyntaxErrorException(str);
    }
    if (str.startsWith("Toplevel input") || str.indexOf("User error") != -1) {
      throw new ProverException("An error occured during the proof:\n" + str + "\n");
    }
  }
  
  
  /** {@inheritDoc} */
  @Override
  public void undo(final ITopLevel itl) throws AProverException {
    if (isProofMode(itl)) {
      try {
        sendCommand(itl, "Undo 1.");
      }
      catch (Exception e) {
        sendCommand(itl, "Abort.");
      }
    }
    else {
      sendCommand(itl, "Back 1.");
    }
  }  


  
  /** {@inheritDoc} */
  @Override
  public int hasToSkipUndo(final ITopLevel itl, 
                           final IDocument document, 
                           final String cmd, 
                           final int beg, final int end) {

    int res;
    res = fProofHandler.hasToSkip(this, itl, document, cmd, beg, end);
    if (res != IProverTopLevel.DONT_SKIP) {
      return res;
    }
    if (fModuleName != null) {
      // fetch the end of a module
      if ((cmd.indexOf("Module " + fModuleName) != -1) ||
        (cmd.indexOf("Module Type " + fModuleName) != -1) ||
        (cmd.indexOf("Section " + fModuleName) != -1)) {
        fModuleName = null;
        return IProverTopLevel.DONT_SKIP;
      }
      return IProverTopLevel.SKIP_AND_CONTINUE;
    }
    if (cmd.trim().startsWith("End ")) {
      // we will have to skip a module :)
      fModuleName = cmd.substring(4, 
                                  cmd.length() - 1);
      return IProverTopLevel.SKIP_AND_CONTINUE;
    }
    
    // the commands to skip
    final String [] vernac = {"Proof", "Show ", "Print "};
    for (int i = 0; i < vernac.length; i++) {
      if (cmd.startsWith(vernac[i])) {
        return IProverTopLevel.SKIP;
      }
    }
    
    // in doubt we evaluate
    return IProverTopLevel.DONT_SKIP;
  }

  

  /** {@inheritDoc} */
  @Override
  public int hasToSkipSendCommand(final ITopLevel itl, 
                                  final IDocument doc, 
                                  final String cmd, 
                                  final int beg, final int end) {
    int res;
    res = fProofHandler.hasToSend(this, itl, doc, cmd, beg, end);
    if (res != IProverTopLevel.DONT_SKIP) {
      return res;
    }
    return IProverTopLevel.DONT_SKIP;
  }
  
  /** {@inheritDoc} */
  @Override
  public String[] getCommands(final String top, 
                              final String[] path) {
    String [] cmds;
    if (path != null) {
      cmds = new String[2 + path.length * 2];
      
      for (int i = 0; i < path.length; i++) {
        final int pos = (2 * (i + 1));
        cmds[pos] = "-I";
        cmds[pos + 1] = path[i];
      }
      
    }
    else {
      cmds = new String[2];
    }
    cmds[0] = top;
    cmds[1] = "-emacs";
    return cmds;
  }
}
