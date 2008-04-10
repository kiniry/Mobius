package mobius.prover.gui.actions;

import mobius.prover.gui.ProverFileContext;
import mobius.prover.gui.TopLevelManager;
import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.ui.IEditorPart;


/**
 * The action to send a back command to the toplevel.
 *
 * @author J. Charles (julien.charles@inria.fr)
 */
public class BackAction extends AProverAction {

  /** {@inheritDoc} */
  @Override
  public void trigger() {
    showTopView();    
    final IEditorPart ed = getActiveEditor();
    if (ed instanceof ProverEditor) {
      final ProverEditor ce = (ProverEditor) ed;
      TopLevelManager.getInstance().regress(new ProverFileContext(ce));      
    }
  }
}
