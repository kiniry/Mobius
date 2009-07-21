/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;

import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.ITextViewer;



/**
 * This class is responsible for action that is performed after
 * a double click event in a bytecode editor window. This triggers a
 * synchronization action which relates the position clicked within the
 * bytecode editor to the source code in the corresponding Java file editor.
 *
 * @author   Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 * @see    BytecodeDocument
 */
public class BytecodeDoubleClickStrategy implements ITextDoubleClickStrategy {

  /**
   * This method implements the reaction on the double click in
   * a bytecode editor. It synchronizes the position clicked within the
   * bytecode editor to the source code in the corresponding Java file
   * editor. Most the information about the selected area is not used.
   * Only the position of the cursor is taken into account.
   *
   * @param a_selection the selected area of the bytecode document
   */
  public final void doubleClicked(final ITextViewer a_selection) {
    final int pos = a_selection.getSelectedRange().x;

    if (pos < 0)
      return;

    final BytecodeDocument bDoc = (BytecodeDocument)a_selection.getDocument();
    bDoc.synchronizeBS(pos);
  }
}
