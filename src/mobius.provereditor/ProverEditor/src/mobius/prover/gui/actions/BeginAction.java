package mobius.prover.gui.actions;

import mobius.prover.gui.ProverFileContext;
import mobius.prover.gui.TopLevelManager;
import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.ui.IEditorPart;


/**
 * The action to start a new toplevel.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class BeginAction extends AProverAction {
  

  /** {@inheritDoc} */
  @Override
  public void trigger() {
    showTopView();
    
    final IEditorPart ed = getActiveEditor();
    if (ed instanceof ProverEditor) {
      final TopLevelManager ctm = TopLevelManager.getInstance();
      if (ctm != null) {
        ctm.reset(new ProverFileContext((ProverEditor)ed));
      }
    }
  }
  

  /** {@inheritDoc} */
  @Override
  public boolean isEnabled() {
    final IEditorPart ed = getActiveEditor();
    return (ed instanceof ProverEditor); 
  }
  
}
