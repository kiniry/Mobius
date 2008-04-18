package mobius.prover.gui.actions;

import mobius.prover.gui.ProverFileContext;
import mobius.prover.gui.TopLevelManager;
import mobius.prover.gui.editor.BasicRuleScanner;
import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.plugins.AProverTranslator;

import org.eclipse.jface.text.rules.IToken;
import org.eclipse.ui.IEditorPart;

/**
 * Jump backward: used while inspecting a file.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class JumpBackward extends AProverAction {
  /**
   * The method executed when jump is triggered.
   * Jump to the previous sentence in the editor.
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
    }
    if (parser == null) {
      return; // second try we give up...
    }    
    parser.setRange(pfc.getDocument(), 0, oldlimit - 1);
    IToken tok; int pos = 0;
    while ((tok = parser.nextToken()) != null) {
      if (tok.isEOF()) {
        break;
      }
      if (tok == AProverTranslator.SENTENCE_TOKEN) {
        pos = parser.getTokenOffset() + parser.getTokenLength();  
      }
    } 
    pfc.getViewer().setSelectedRange(pos, 0);
    pfc.getViewer().revealRange(pos, 0);
    return;
  }
}
