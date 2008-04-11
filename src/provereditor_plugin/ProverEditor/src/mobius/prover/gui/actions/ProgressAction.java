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


/**
 * An action to progress in ProverEditor.
 *
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ProgressAction extends AProverAction {

  /** {@inheritDoc} */
  @Override
  public void trigger() {
    showTopView();
    
    final IEditorPart ed = getActiveEditor();
    if (ed instanceof ProverEditor) {
      final ProverEditor ce = (ProverEditor) ed;
      final Job job = new UpdateJob(ce);
      job.schedule();
      
    }    
  }
  
  
  /**
   * The Job to send a progress action to the top level.
  
   */
  private class UpdateJob extends Job {
    /** The target editor where to progress. */
    private ProverEditor fEditor;
    
    /**
     * Create a new Job to progress.
     * @param editor The target editor
     */
    public UpdateJob(final ProverEditor editor) {
      super("TopLevel is progressing...");
      fEditor = editor;
    }  
    
    /** {@inheritDoc} */
    @Override
    public IStatus run(final IProgressMonitor monitor) {      
      TopLevelManager.getInstance().progress(new ProverFileContext(fEditor));
      return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
    }
  }


  
  


}
