package mobius.prover.gui.actions;

import mobius.prover.gui.ProverFileContext;
import mobius.prover.gui.TopLevelManager;
import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;


/**
 * The action to start a new toplevel.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class BeginAction extends AProverAction {
  

  /** {@inheritDoc} */
  @Override
  public void trigger() {
    try {
      PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().showView("ProverEditor.topview");
    } 
    catch (PartInitException e) {  
      
    }
    final IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
    final IEditorPart ed = ap.getActiveEditor();
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
    final IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
    final IEditorPart ed = ap.getActiveEditor();
    return (ed instanceof ProverEditor); 
  }
  
}
