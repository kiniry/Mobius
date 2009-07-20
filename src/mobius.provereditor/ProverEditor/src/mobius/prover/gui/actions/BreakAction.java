package mobius.prover.gui.actions;

import mobius.prover.gui.TopLevelManager;
import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.ui.IEditorPart;


/**
 * The action that send a break command to the top level.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class BreakAction extends AProverAction {
  
  /** {@inheritDoc} */
  @Override
  public void trigger() {
    showTopView();
    final IEditorPart ed = getActiveEditor();
    if (ed instanceof ProverEditor) {
      TopLevelManager.getInstance().doBreak();      
    }
  }

}
