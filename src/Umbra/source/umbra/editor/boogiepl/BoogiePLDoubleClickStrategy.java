package umbra.editor.boogiepl;

import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.ITextViewer;



/**
 * This class is responsible for action that is executed after
 * double clicking in BoogiePL editor window. Synchronization
 * to Java code window is then made.
 *
 * @author   Samuel Willimann
 * @see    BoogiePLDocument
 */
public class BoogiePLDoubleClickStrategy implements ITextDoubleClickStrategy {

  /**
   * TODO
   */
  public void doubleClicked(ITextViewer part) {
    int pos = part.getSelectedRange().x;

    if (pos < 0)
      return;

    BoogiePLDocument bDoc = (BoogiePLDocument)part.getDocument();
    bDoc.synchronizeBS(pos);
  }
}
