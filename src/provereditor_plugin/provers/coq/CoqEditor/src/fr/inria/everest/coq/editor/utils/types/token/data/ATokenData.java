package fr.inria.everest.coq.editor.utils.types.token.data;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;

import prover.gui.editor.BasicRuleScanner;
import prover.gui.editor.ProverEditor;
import prover.gui.editor.outline.types.ProverType;

public abstract class ATokenData {

	String fText;
	protected int fOffset;
	protected int fLen;
	protected IDocument fDoc;
	
	public ATokenData spawn(IDocument doc, BasicRuleScanner scanner) {
		ATokenData td;
		try {
			 td = (ATokenData) this.clone();
			 td.fOffset = scanner.getTokenOffset();
			 td.fLen = scanner.getTokenLength();
			 td.fDoc = doc;
			 try {
				td.fText = td.fDoc.get(td.fOffset, td.fLen);
			} catch (BadLocationException e) {
				td.fText = "---> Undefined";
			}
			 return td;
		} catch (CloneNotSupportedException e) {
			e.printStackTrace();
		}
		
		return null;
	}
	public abstract ProverType parse(ProverEditor editor) ;
	public int getEnd() {
		return fOffset + fLen;
	}
}


