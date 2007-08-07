/*
 * @title       "BoogiePL in Umbra"
 * @description "BoobiePL support for Umbra bytecode editor"
 * @copyright   ""
 * @license     ""
 */
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
   * This method implements the reaction on the double click in
   * a BoogiePL editor. It synchronizes the position clicked within the
   * BoogiePL editor to the source code in the corresponding Java file
   * editor. Most the information about the selected area is not used.
   * Only the position of the cursor is taken into account.
   *
   * TODO check if it's correct, especially with the definition of
   * the {@ref BoogiePLDocument#synchronizeBS(int)}.
   *
   * @param a_selection the selected area of the bytecode document
   */
  public final void doubleClicked(final ITextViewer a_selection) {
    final int pos = a_selection.getSelectedRange().x;

    if (pos < 0)
      return;

    final BoogiePLDocument bDoc = (BoogiePLDocument)a_selection.getDocument();
    bDoc.synchronizeBS(pos);
  }
}
