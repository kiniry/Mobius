package fr.inria.everest.coq.editor.utils;

import java.util.LinkedList;
import java.util.Stack;

import org.eclipse.jface.text.IDocument;

import fr.inria.everest.coq.editor.BasicCoqTop;

import prover.exec.ITopLevel;
import prover.plugins.IProverTopLevel;

public class ProofHandler {
	private LinkedList proofList = new LinkedList();
	private int fLast;
	private Proof fCurrentProof;
	private Stack fProofs = new Stack();
	public int hasToSend(BasicCoqTop top, ITopLevel itl, IDocument doc, String cmd, int beg, int end) {		
		if(top.isProofMode(itl)) {
			if (fCurrentProof == null) {
				proofList.addFirst(itl.getErrBuffer().split(" ")[0]);
				fCurrentProof = new Proof();
				fCurrentProof.fBeginPos = beg;
				fCurrentProof.fNamePos = fLast;
			}
			else {
				if (!(itl.getErrBuffer().startsWith(proofList.getFirst().toString()))) {
					proofList.addFirst(itl.getErrBuffer().split(" ")[0]);
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
		if(fCurrentProof != null) {
			// we might be within a proof
			if(!top.isProofMode(itl)) {
				// we are at the end of a proof
				if(fCurrentProof.fNamePos != beg)
					return IProverTopLevel.SKIP_AND_CONTINUE;
				else {
					fCurrentProof = null;
					return IProverTopLevel.DONT_SKIP;
				}
			}
			else  {
				
				return IProverTopLevel.DONT_SKIP;
			}
		}
		else {
			// we are outside the proof or at the begining of one
			if(fProofs.size() > 0) {
				Proof p = (Proof)fProofs.peek();
				if(p.isWithinProof(beg)) {
					if(p.fNamePos == beg) {
						fProofs.pop();
						return IProverTopLevel.DONT_SKIP;
					}
					return IProverTopLevel.SKIP_AND_CONTINUE;
				}
			}	
		}
		return IProverTopLevel.DONT_SKIP;
	}
}
