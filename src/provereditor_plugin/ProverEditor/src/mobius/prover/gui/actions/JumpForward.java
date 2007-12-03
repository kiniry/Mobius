package mobius.prover.gui.actions;

import mobius.prover.gui.ProverFileContext;
import mobius.prover.gui.TopLevelManager;
import mobius.prover.plugins.AProverTranslator;

import org.eclipse.jface.text.rules.IToken;
import org.eclipse.ui.IEditorPart;

import prover.gui.editor.BasicRuleScanner;
import prover.gui.editor.ProverEditor;

public class JumpForward extends AProverAction {
	/**
	 * The method executed when jump is triggered.
	 * Jump to the next sentence in the editor.
	 */
	public void trigger() {
	    IEditorPart ep = getActiveEditor();
		if(! (ep instanceof ProverEditor)) {
			return;
		}
		ProverFileContext pfc = new ProverFileContext((ProverEditor) ep);
		TopLevelManager tlm = TopLevelManager.getInstance();
		int oldlimit = pfc.viewer.getSelectedRange().x;
		BasicRuleScanner parser;
		if((parser = tlm.getParser()) == null) {
			tlm.reset(pfc);
		}
		if((parser = tlm.getParser()) == null) {
			return; // second try we give up...
		}		
		parser.setRange(pfc.doc, oldlimit, pfc.doc.getLength() - oldlimit);
		IToken tok;
		do {
			tok = parser.nextToken();
		} while(tok != AProverTranslator.SENTENCE_TOKEN && (!tok.isEOF()));
		if(!tok.isEOF()) {
			int pos = parser.getTokenOffset() + parser.getTokenLength();
			pfc.viewer.setSelectedRange(pos, 0);
			pfc.viewer.revealRange(pos, 0);
		}
		return;
	}

}
