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
import org.eclipse.ui.progress.UIJob;


/**
 * An action to progress until the end of the file.
 *
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ProgressEndAction  extends AProverAction {


  /** {@inheritDoc} */
  @Override
  public void trigger() {
    
    showTopView();
    final IEditorPart editor = getActiveEditor();
    if (editor instanceof ProverEditor) {
      final Job j = new TopLevelJob((ProverEditor) editor);
      j.schedule();    
    }    
  }
  
  /**
   * A job to execute the action.
   * @author J. Charles (julien.charles@inria.fr)
   */
  private static class TopLevelJob extends Job {
    /** the target editor. */
    private final ProverEditor fEditor;
    
    /**
     * Initialize a toplevel job associated with an editor.
     * @param editor the current editor associated with 
     * the top level
     */
    public TopLevelJob(final ProverEditor editor) {
      super("TopLevel Editor is computing...");
      fEditor = editor;
    }
    
    /** {@inheritDoc} */
    @Override
    protected IStatus run(final IProgressMonitor monitor) {
      
      boolean notlastres = true;
      final TopLevelManager top = TopLevelManager.getInstance();
      if (top == null) {
        System.out.println("nul");
      }
      while (notlastres) {
        notlastres = top.progress(new ProverFileContext(fEditor));
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
  }
}
