package mobius.prover.gui.actions;

import mobius.prover.gui.ProverFileContext;
import mobius.prover.gui.TopLevelManager;
import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.UIJob;


/**
 * An action to progress until the end of the file.
 *
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ProgressEndAction  extends AProverAction {
  /** the target editor. */
  private ProverEditor fEditor;

  /** {@inheritDoc} */
  @Override
  public void trigger() {
    final IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
    
    try {
      ap.showView("ProverEditor.topview");
    } 
    catch (PartInitException e) {  }
    final IEditorPart editor = ap.getActiveEditor();
    if (editor instanceof ProverEditor) {
      fEditor = (ProverEditor) editor;
      final Job j = new Job("TopLevel Editor is computing...") {

        protected IStatus run(final IProgressMonitor monitor) {
          boolean notlastres = true;
          if (TopLevelManager.getInstance() == null) {
            System.out.println("nul");
          }
          while (notlastres) {
            notlastres = TopLevelManager.getInstance().progress(new ProverFileContext(fEditor));
            final UIJob job = new UIJob("CoqEditor is updating...") {
              public IStatus runInUIThread(final IProgressMonitor monitor) {
                return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
              }
            };
            job.schedule();
            try {
              job.join();
            
            } 
            catch (InterruptedException e) {
              e.printStackTrace();
            }
          }
          return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
        }
        
      };
      j.schedule();    
    }    
  }
}
