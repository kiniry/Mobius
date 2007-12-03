package mobius.prover.gui.actions;

import mobius.prover.gui.ProverFileContext;
import mobius.prover.gui.TopLevelManager;
import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;



/**
 * This Class trigger an action to reset the current proof.
 *
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ResetAction extends AProverAction {

  /** {@inheritDoc} */
  @Override
  public void trigger() {
    try {
      PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().showView("ProverEditor.topview");
    } 
    catch (PartInitException e) {  }
    final IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
    final IEditorPart ed = ap.getActiveEditor();
    if (!(ed instanceof ProverEditor)) {
      return;
    }
    final ProverEditor ce = (ProverEditor) ed;
    TopLevelManager.getInstance().reset(new ProverFileContext(ce));    
  }
}
