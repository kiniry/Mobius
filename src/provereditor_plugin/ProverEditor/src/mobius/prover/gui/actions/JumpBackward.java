package mobius.prover.gui.actions;

import mobius.prover.gui.ProverFileContext;
import mobius.prover.gui.TopLevelManager;
import mobius.prover.plugins.AProverTranslator;

import org.eclipse.jface.text.rules.IToken;
import org.eclipse.ui.IEditorPart;

import prover.gui.editor.BasicRuleScanner;
import prover.gui.editor.ProverEditor;

public class JumpBackward extends AProverAction {
	/**
	 * The method executed when jump is triggered.
	 * Jump to the previous sentence in the editor.
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
		parser.setRange(pfc.doc, 0, oldlimit - 1);
		IToken tok; int pos = 0;
		while((tok = parser.nextToken()) != null && (!tok.isEOF())) {
			if(tok == AProverTranslator.SENTENCE_TOKEN) {
				pos = parser.getTokenOffset() + parser.getTokenLength();	
			}
		} 
		pfc.viewer.setSelectedRange(pos, 0);
		pfc.viewer.revealRange(pos, 0);
		return;
	}
}
