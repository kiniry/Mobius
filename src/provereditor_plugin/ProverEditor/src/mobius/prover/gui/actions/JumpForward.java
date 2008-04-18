package mobius.prover.gui.actions;

import mobius.prover.gui.ProverFileContext;
import mobius.prover.gui.TopLevelManager;
import mobius.prover.gui.editor.BasicRuleScanner;
import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.plugins.AProverTranslator;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.ui.IEditorPart;


/**
 * Jump to the next sentence: useful to inspect a file.
 * @author J. Charles (julien.charles@inria.fr)
 */
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
    final int oldlimit = pfc.getViewer().getSelectedRange().x;
    BasicRuleScanner parser = tlm.getParser();
    if (parser == null) {
      tlm.reset(pfc);
      parser = tlm.getParser();
      if (parser == null) {
        return; // second try we give up...
      }   
    }
    final IDocument doc = pfc.getDocument();
    parser.setRange(doc, oldlimit, doc.getLength() - oldlimit);
    IToken tok;
    do {
      tok = parser.nextToken();
    } while(tok != AProverTranslator.SENTENCE_TOKEN && (!tok.isEOF()));
    if (!tok.isEOF()) {
      final int pos = parser.getTokenOffset() + parser.getTokenLength();
      pfc.getViewer().setSelectedRange(pos, 0);
      pfc.getViewer().revealRange(pos, 0);
    }
    return;
  }

}
