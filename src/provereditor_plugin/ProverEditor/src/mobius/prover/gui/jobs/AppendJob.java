package mobius.prover.gui.jobs;


import mobius.prover.gui.editor.BasicRuleScanner;
import mobius.prover.gui.editor.BasicTextAttribute;
import mobius.prover.gui.editor.BasicTextPresentation;
import mobius.prover.gui.editor.IColorConstants;
import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.UIJob;



/**
 * A job to add some text to the specified document. 
 * It uses a fScanner to highlight the words.
 * To schedule this Job the {@link #prepare()} method shall be used.
 */
public class AppendJob extends UIJob implements IColorConstants, IAppendJob {
  /** The string to append to the document */
  private StringBuffer fStrToAppend;
  /** The document to modify */
  private IDocument fDoc;
  /** The viewer to target */
  private TextViewer fViewer;
  
  /** The presentation containing the highlight informations */
  private BasicTextPresentation fPresentation;
  /** The scanner to colour the words. */
  private BasicRuleScanner fScanner;
  /** The length of the document before any modifications. */
  private int fLen;
  /** The part that has to have focus after the end of the append job */
  private IWorkbenchPart fEditor;
  
  /**
   * Create a new AppendJob.
   * @param scanner The scanner used to decide which word to highlight
   * @param tp The information about the document that shall be updated
   */
  public AppendJob(ProverEditor pe, BasicRuleScanner scanner, BasicTextPresentation tp) {
    super("Updating view");
    fStrToAppend = new StringBuffer();
    fPresentation = (BasicTextPresentation)tp.clone();
    fViewer = tp.getTextViewer();
    fDoc = fViewer.getDocument();
    fScanner = scanner;
    fEditor = pe;
    
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
    SimpleAppendJob saj = new SimpleAppendJob(fViewer);
    saj.add(fStrToAppend);
    fLen = fDoc.getLength();
    saj.schedule();
    schedule();
  }
  
  
  /*
   *  (non-Javadoc)
   * @see org.eclipse.ui.progress.UIJob#runInUIThread(org.eclipse.core.runtime.IProgressMonitor)
   */
  public IStatus runInUIThread(IProgressMonitor monitor) {
    if(fScanner != null) {
      fScanner.setRange(fDoc, fLen, fStrToAppend.length());
      IToken tok;
      while (!(tok = fScanner.nextToken()).isEOF()) {
        if(tok != fScanner.getDefaultReturnToken()) {
          BasicTextAttribute bta = (BasicTextAttribute)tok.getData();
          fPresentation.mergeStyleRange(new StyleRange(fScanner.getTokenOffset(), 
              fScanner.getTokenLength(), bta.getForeground(), 
              bta.getBackground()));
          
        }
        
      }
    }  
    fViewer.changeTextPresentation(fPresentation, true);
    PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().activate(fEditor);
    return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
  }
  
}