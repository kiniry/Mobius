package mobius.prover.gui;

import mobius.prover.ProverEditorPlugin;
import mobius.prover.gui.editor.BasicPresentationReconciler;
import mobius.prover.gui.editor.BasicTextPresentation;
import mobius.prover.gui.editor.IColorConstants;
import mobius.prover.gui.jobs.ColorAppendJob;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.progress.UIJob;

/**
 * The base top level manager file. Handle the base initialisation, 
 * greetings, locking.
 * @author J. Charles (julien.charles@inria.fr)
 */
public abstract class ABaseTopLevelManager extends ViewPart implements IColorConstants {
  /** the greetings message. */
  public static final String GREETINGS = "This is ProverEditor version " + 
                      ProverEditorPlugin.MAJORVERSION + "." + 
                      ProverEditorPlugin.VERSION + "." + 
                      ProverEditorPlugin.SUBVERSION + " !\n";   

  
  /** the lock system to avoid race conditions. */
  private boolean fLock;

  /* The text viewer used to show the prover state related fields: */
  /** the text viewer to show the state of the prover. */
  private TextViewer fStateText;

  /** the current text presentation associated with the text viewer. */
  private BasicTextPresentation fStatePres;

  /**
   * Sets the lock.
   * @return <code>true</code> if everything went well, 
   *  <code>false</code> if the lock was already set.
   */
  protected synchronized boolean lock() {
    if (fLock) {
      return false;
    }
    fLock = true; 
    return true;
  }
  
  /**
   * Unsets the lock.
   */
  protected synchronized void unlock() {
    fLock = false;
  }
  
  
  /** {@inheritDoc} */
  @Override
  public void setFocus() {
    
  }
  
  /** {@inheritDoc} */
  @Override
  public void createPartControl(final Composite parent) {
    IDocument doc = null;
    if (fStateText == null) {
      doc = new Document("");
    }
    else {
      doc = fStateText.getDocument();
    }
    fStateText = new TextViewer(parent, SWT.V_SCROLL);
    fStateText.setEditable(false);    
    fStateText.setDocument(doc);
    fStatePres = new BasicTextPresentation(fStateText);

    new ColorAppendJob(fStatePres, GREETINGS, VIOLET).prepare();

  }
  /**
   * The current text presentation 
   * associated with the text viewer.
   * @return a valid text presentation 
   */
  public BasicTextPresentation getTxtPresentation() {
    return fStatePres;
  }
  
  /**
   * The class UpdateJob is used to update the view once it has changed
   * internally.
   */
  protected static class UpdateJob extends UIJob {
    /** the limit of the update. */
    private int fLimit;
    /** the presentation reconciler to update. */
    private BasicPresentationReconciler fReconciler;
    /** the context associated with the current top level. */
    private final ProverFileContext fProverContext;

    
    /**
     * Create a job to update a presentation reconciler in a UIThread context.
     * @param reconciler The reconciler to update.
     * @param proverContext The context in which the job is created.
     * @param limit The limit of the update.
     */
    public UpdateJob(final BasicPresentationReconciler reconciler,
                     final ProverFileContext proverContext,
                     final int limit) {
      super("Updating text");
      fReconciler = reconciler;
      fLimit = limit;
      fProverContext = proverContext;
    }

    /**
     * Create a job to update a presentation reconciler in a UIThread context.
     * @param reconciler The reconciler to update.
     * @param proverContext The context in which the job is created.
     */
    public UpdateJob(final BasicPresentationReconciler reconciler,
                     final ProverFileContext proverContext) {
      this(reconciler, proverContext, reconciler.getDocument().getLength());
    }
    
    /** {@inheritDoc} */
    @Override
    public IStatus runInUIThread(final IProgressMonitor monitor) {
      fReconciler.everythingHasChanged(0, fLimit); 
      final IWorkbenchWindow win = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
      final IWorkbenchPage page = win.getActivePage();
      page.activate(fProverContext.getEditor());
      return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
    }
    
  }  
}
