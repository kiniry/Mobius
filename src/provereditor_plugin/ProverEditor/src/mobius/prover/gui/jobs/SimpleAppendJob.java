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
 */
public class SimpleAppendJob extends UIJob implements IColorConstants, IAppendJob {
  /** The string to append to the document */
  private StringBuffer fStrToAppend;
  /** The document to modify */
  private IDocument fDoc;
  /** The viewer to target */
  private TextViewer fViewer;
  
  
  /**
   * Create a job to append text to the document in the viewer.
   * @param viewer The viewer to append text to.
   */
  public SimpleAppendJob(TextViewer viewer) {
    super("Updating view");
    fStrToAppend = new StringBuffer();
    fViewer = viewer;
    fDoc = fViewer.getDocument();
    
  }
  
  /*
   *  (non-Javadoc)
   * @see prover.gui.jobs.IAppendJob#add(java.lang.StringBuffer)
   */
  public void add(StringBuffer str) {
    fStrToAppend.append(str);
  }
  
  /*
   *  (non-Javadoc)
   * @see prover.gui.jobs.IAppendJob#add(java.lang.String)
   */
  public void add(String str) {
    add(new StringBuffer(str));
  }

  /*
   *  (non-Javadoc)
   * @see prover.gui.jobs.IAppendJob#getLength()
   */
  public int getLength() {
    return fStrToAppend.length();
  }
  
  /*
   *  (non-Javadoc)
   * @see prover.gui.jobs.IAppendJob#prepare()
   */
  public void prepare() {  
    schedule();
  }
  
  /*
   *  (non-Javadoc)
   * @see org.eclipse.ui.progress.UIJob#runInUIThread(org.eclipse.core.runtime.IProgressMonitor)
   */
  public IStatus runInUIThread(IProgressMonitor monitor) {
    int len = fDoc.getLength();
    try {
      fDoc.replace(len, 0, fStrToAppend.toString());
    } catch (BadLocationException e) {
      e.printStackTrace();
    }
    fViewer.setTopIndex(len - 1);
    return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
  }
  
}