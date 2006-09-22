package fr.inria.everest.coq.editor.utils;

import java.util.Stack;

import org.eclipse.jface.text.IDocument;

import prover.exec.ITopLevel;
import prover.plugins.IProverTopLevel;
import fr.inria.everest.coq.editor.BasicCoqTop;

public class ProofHandler {
	/** the name of the proof as written in the prompt */
	private String proofName = "";
	/** the position of the previous command send through the proof handler */
	private int fLast = 0;
	/** the proof currently edited, can be <code>null</code> */
	private Proof fCurrentProof;
	/** the proof currently being skipped, can be <code>null</code> */
	private Proof fCurrentProofToSkip;
	/** the stack of the previously encountered proofs... */
	private Stack fProofs = new Stack();
	
	
	
	public int hasToSend(BasicCoqTop top, ITopLevel itl, IDocument doc, String cmd, int beg, int end) {		
		if(top.isProofMode(itl)) {
			if (fCurrentProof == null) {
				proofName = itl.getErrBuffer().split(" ")[0];
				fCurrentProof = new Proof(fLast, beg);
			}
			else {
				// case of imbricated proofs
				if (!(itl.getErrBuffer().startsWith(proofName))) {
					proofName = itl.getErrBuffer().split(" ")[0];
					fCurrentProof.fEndPos = beg;
					fProofs.push(fCurrentProof);
					fCurrentProof = null;
				}
			}
		}
		else if((!top.isProofMode(itl)) && (fCurrentProof != null)) {
			fCurrentProof.fEndPos = beg;
			fProofs.push(fCurrentProof);
			fCurrentProof = null;
		}
		fLast = beg;
		return IProverTopLevel.DONT_SKIP;

	}
	
	public int hasToSkip(BasicCoqTop top, ITopLevel itl, IDocument document, String cmd, int beg, int end) {
		
		if (fCurrentProof != null) {
			if(!top.isProofMode(itl)) {
				// we were not so long ago editing a proof. we have to clean everything up
				fCurrentProof.fEndPos = end;
				fProofs.push(fCurrentProof);
				fCurrentProof = null;
			}
			else {
				//we are currently editing a proof, we have to skip it
				if(fCurrentProof.isWithinProof(beg)) {
					return IProverTopLevel.DONT_SKIP;
				}
				else {
					fCurrentProof = null;
				}
			}
		}
		
		if(fCurrentProofToSkip != null) {
			// we might be within a proof we want to skip
			// we are also editing a proof
			if(fCurrentProofToSkip.fNamePos != beg)
				return IProverTopLevel.SKIP_AND_CONTINUE;
			else {
				fCurrentProofToSkip = null;
			}
		}

		// we are outside the proof or at the begining of one
		if(fProofs.size() > 0) {
			Proof p = (Proof)fProofs.peek();
			if(p.isWithinProof(beg)) {
				if(p.fNamePos == beg) {
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
