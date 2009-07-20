package mobius.prover.coq.utils;

import java.util.Stack;

import mobius.prover.coq.BasicCoqTop;
import mobius.prover.exec.ITopLevel;
import mobius.prover.plugins.IProverTopLevel;

import org.eclipse.jface.text.IDocument;


public class ProofHandler {
  /** the name of the proof as written in the prompt. */
  private String fProofName = "";
  /** the position of the previous command send through the proof handler. */
  private int fLast;
  /** the proof currently edited, can be <code>null</code>. */
  private Proof fCurrentProof;
  /** the proof currently being skipped, can be <code>null</code>. */
  private Proof fCurrentProofToSkip;
  /** the stack of the previously encountered proofs... */
  private Stack<Proof> fProofs = new Stack<Proof>();
  
  
  
  public int hasToSend(final BasicCoqTop top, final ITopLevel itl, 
                       final IDocument doc, final String cmd, 
                       final int beg, final int end) {    
    if (top.isProofMode(itl)) {
      if (fCurrentProof == null) {
        fProofName = itl.getErrBuffer().split(" ")[0];
        fCurrentProof = new Proof(fLast, beg);
      }
      else {
        // case of imbricated proofs
        if (!(itl.getErrBuffer().startsWith(fProofName))) {
          fProofName = itl.getErrBuffer().split(" ")[0];
          fCurrentProof.fEndPos = beg;
          fProofs.push(fCurrentProof);
          fCurrentProof = null;
        }
      }
    }
    else if ((!top.isProofMode(itl)) && (fCurrentProof != null)) {
      fCurrentProof.fEndPos = beg;
      fProofs.push(fCurrentProof);
      fCurrentProof = null;
    }
    fLast = beg;
    return IProverTopLevel.DONT_SKIP;

  }
  
  public int hasToSkip(final BasicCoqTop top, final ITopLevel itl, 
                       final IDocument document, final String cmd, 
                       final int beg, final int end) {
    
    if (fCurrentProof != null) {
      if (!top.isProofMode(itl)) {
        // we were not so long ago editing a proof. we have to clean everything up
        fCurrentProof.fEndPos = end;
        fProofs.push(fCurrentProof);
        fCurrentProof = null;
      }
      else {
        //we are currently editing a proof, we have to skip it
        if (fCurrentProof.isWithinProof(beg)) {
          return IProverTopLevel.DONT_SKIP;
        }
        else {
          fCurrentProof = null;
        }
      }
    }
    
    if (fCurrentProofToSkip != null) {
      // we might be within a proof we want to skip
      // we are also editing a proof
      if (fCurrentProofToSkip.fNamePos != beg) {
        return IProverTopLevel.SKIP_AND_CONTINUE;
      }
      else {
        fCurrentProofToSkip = null;
      }
    }

    // we are outside the proof or at the begining of one
    if (fProofs.size() > 0) {
      final Proof p = (Proof)fProofs.peek();
      if (p.isWithinProof(beg)) {
        if (p.fNamePos == beg) {
          // one line proofs are kind of nonsense.
          return IProverTopLevel.DONT_SKIP;
        }
        else {
          fCurrentProofToSkip = (Proof)fProofs.pop();
        }
        return IProverTopLevel.SKIP_AND_CONTINUE;
      }  
    }
    return IProverTopLevel.DONT_SKIP;
  }
}
