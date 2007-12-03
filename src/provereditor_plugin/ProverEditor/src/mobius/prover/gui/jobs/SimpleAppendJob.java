package mobius.prover.gui.jobs;


import mobius.prover.gui.editor.IColorConstants;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.ui.progress.UIJob;


/**
 * A Job to append text to the specified document contained in a viewer.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class SimpleAppendJob extends UIJob implements IColorConstants, IAppendJob {
  /** The string to append to the document. */
  private StringBuffer fStrToAppend;
  /** The document to modify. */
  private IDocument fDoc;
  /** The viewer to target. */
  private TextViewer fViewer;
  
  
  /**
   * Create a job to append text to the document in the viewer.
   * @param viewer The viewer to append text to.
   */
  public SimpleAppendJob(final TextViewer viewer) {
    super("Updating view");
    fStrToAppend = new StringBuffer();
    fViewer = viewer;
    fDoc = fViewer.getDocument();
    
  }
  
  /** {@inheritDoc} */
  @Override
  public void add(final StringBuffer str) {
    fStrToAppend.append(str);
  }
  
  /** {@inheritDoc} */
  @Override
  public void add(final String str) {
    add(new StringBuffer(str));
  }

  /** {@inheritDoc} */
  @Override
  public int getLength() {
    return fStrToAppend.length();
  }
  

  /** {@inheritDoc} */
  @Override
  public void prepare() {  
    schedule();
  }
 
  /** {@inheritDoc} */
  @Override
  public IStatus runInUIThread(final IProgressMonitor monitor) {
    final int len = fDoc.getLength();
    try {
      fDoc.replace(len, 0, fStrToAppend.toString());
    } 
    catch (BadLocationException e) {
      e.printStackTrace();
    }
    fViewer.setTopIndex(len - 1);
    return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
  }
  
}
