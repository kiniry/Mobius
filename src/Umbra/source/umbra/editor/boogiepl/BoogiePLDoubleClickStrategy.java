package umbra.editor.boogiepl;

import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.ITextViewer;



/**
 * This class is responsible for action that is executed after
 * double clicking in BoogiePL editor window. Synchronization
 * to Java code window is then made.
 *
 * @author   Samuel Willimann  (wsamuel@student.ethz.ch)
 * @version a-01
 * @see    BoogiePLDocument
 */
public class BoogiePLDoubleClickStrategy implements ITextDoubleClickStrategy {

  /**
   * TODO
   */
  public final void doubleClicked(final ITextViewer part) {
    final int pos = part.getSelectedRange().x;

    if (pos < 0)
      return;

    final BoogiePLDocument bDoc = (BoogiePLDocument)part.getDocument();
    bDoc.synchronizeBS(pos);
  }
}
