package mobius.prover.gui.jobs;


import mobius.prover.gui.editor.BasicTextPresentation;
import mobius.prover.gui.editor.IColorConstants;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;


/**
 * A Job to append some text with the specified color.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ColorAppendJob extends SimpleAppendJob implements IColorConstants, IAppendJob {
  /** The document to modify. */
  private IDocument fDoc;
  /** The viewer to target. */
  private TextViewer fViewer;
  /** The presentation containing the color informations. */
  private BasicTextPresentation fPresentation;
  
  /**
   * Create a new ColorAppendJob.
   * @param presentation The information about the document that shall be updated
   */
  public ColorAppendJob(final BasicTextPresentation presentation) {
    super(presentation.getTextViewer());
    fPresentation = (BasicTextPresentation) presentation.clone();
    fViewer =  presentation.getTextViewer();
    fDoc = fViewer.getDocument();
    
  }
  
  /**
   * Initialize the object with the specified presentation,
   * and then add the specified text with the specified color.
   * @param presentation the document where to append the text
   * @param str some text to append
   * @param col the base color for the text
   */
  public ColorAppendJob(final BasicTextPresentation presentation, 
                        final String str, final Color col) {
    this(presentation);
    add(str, col);
  }
  

  /**
   * Add the specified text, with its associated color.
   * @param str The text to append
   * @param col The color of the text
   */
  public void add(final StringBuffer str, final Color col) {
    final int ol = getLength();
    add(str);
    addColor(ol, str.length() - 1, col);
  }
  
  /**
   * Add the specified text, with its associated color.
   * @param str The text to append
   * @param col The color of the text
   */
  public void add(final String str, final Color col) {
    add(new StringBuffer(str), col);
  }
  
  
  /**
   * Add a color to the text. The offset and length
   * are based on the current string to be append.
   * @param offset The offset to which to add the color
   * @param l the length of the color changing
   * @param col the color to set
   */
  private void addColor(final int offset, final int l, 
                        final Color col)  {
    final int oldlen =  getLength();
    int len = l;
    if (offset >= oldlen)  {
      // really out of bounds
      throw new IllegalArgumentException("AppendJob.addColor: Wrong offset !");
    }
    if (offset + len >= oldlen) { 
      // just a bit out of bounds
      System.err.println("ProverEditor: AppendJob.addColor, Wrong length !");
      System.err.println("ProverEditor: Recovering...");
      len = oldlen - (offset + 1); 
    }  
    fPresentation.mergeStyleRange(new StyleRange(offset + fDoc.getLength(), len, col, WHITE));
    
  }
  

  /** {@inheritDoc} */
  @Override
  public IStatus runInUIThread(final IProgressMonitor monitor) {
    super.runInUIThread(monitor);
    fViewer.changeTextPresentation(fPresentation, true);  
    return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
  }
  
}
