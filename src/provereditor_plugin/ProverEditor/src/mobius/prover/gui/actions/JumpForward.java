package mobius.prover.gui.actions;

import mobius.prover.gui.ProverFileContext;
import mobius.prover.gui.TopLevelManager;
import mobius.prover.gui.editor.BasicRuleScanner;
import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.plugins.AProverTranslator;

import org.eclipse.jface.text.rules.IToken;
import org.eclipse.ui.IEditorPart;


public class JumpForward extends AProverAction {
  /**
   * The method executed when jump is triggered.
   * Jump to the next sentence in the editor.
   */
  public void trigger() {
    final IEditorPart ep = getActiveEditor();
    if (!(ep instanceof ProverEditor)) {
      return;
    }
    final ProverFileContext pfc = new ProverFileContext((ProverEditor) ep);
    final TopLevelManager tlm = TopLevelManager.getInstance();
    final int oldlimit = pfc.fViewer.getSelectedRange().x;
    BasicRuleScanner parser;
    if ((parser = tlm.getParser()) == null) {
      tlm.reset(pfc);
    }
    if ((parser = tlm.getParser()) == null) {
      return; // second try we give up...
    }    
    parser.setRange(pfc.fDoc, oldlimit, pfc.fDoc.getLength() - oldlimit);
    IToken tok;
    do {
      tok = parser.nextToken();
    } while(tok != AProverTranslator.SENTENCE_TOKEN && (!tok.isEOF()));
    if (!tok.isEOF()) {
      final int pos = parser.getTokenOffset() + parser.getTokenLength();
      pfc.fViewer.setSelectedRange(pos, 0);
      pfc.fViewer.revealRange(pos, 0);
    }
    return;
  }

}
