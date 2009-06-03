/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;

import org.eclipse.jface.action.ControlContribution;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;

import bmllib.utils.BMLChangeException;

import umbra.UmbraPlugin;
import umbra.lib.EclipseIdentifiers;
import umbra.lib.FileNames;
import umbra.lib.GUIMessages;
import umbra.lib.UmbraException;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraRepresentationException;

/**
 * This class represents a GUI element that is contributed to the
 * eclipse GUI by the byte code editor. It handles all the edit
 * events and propagates them to the currently edited document
 * so that they are recorded in the internal structures of the document.
 *
 * The objects of this class are generated when a new {@link BytecodeEditor}
 * is brought to life. However, in case the new editor is opened in order
 * to refresh the content of an existing byte code document, then an old
 * {@link BytecodeContribution} object must be reused.
 *
 * FIXME: the cached object is kept in a static variable, this is probably
 *   not enough; https://mobius.ucd.ie/ticket/602
 *
 * @author Wojciech Wąs  (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeContribution extends ControlContribution {

  /**
   * The only object of this class which is currently present in the system.
   */
  private static BytecodeContribution inUse;

  /**
   * The flag which indicates if the current, statically cached
   * {@link BytecodeContribution} should be replaced with a new one.
   * The default value is such that the new object should be generated.
   */
  private boolean my_new_contribution_required = true;

  /**
   * The current byte code editor for which the contribution works.
   */
  private BytecodeEditor my_editor;

  /**
   * This creates the object and stores it in a static variable so that
   * it is available from everywhere through {@link #inUse()} method.
   */
  protected BytecodeContribution() {
    super(EclipseIdentifiers.BYTECODE_CONTRIBUTION_IDENTIFIER);
    if (FileNames.DEBUG_MODE && inUse != null) {
      UmbraPlugin.messagelog("Second BytecodeContribution!!!");
    }
    inUse = this;
  }

  /**
   * The factory method which generates the {@link BytecodeContribution}
   * to be used by the rest of the Umbra editor. This method checks if
   * there is a {@link BytecodeContribution} object cached and in that
   * case it asks the object if it should be replaced by a new one. In case
   * it should not, the currently cached object is returned. Otherwise,
   * a new object is created.
   *
   * @return an {@link BytecodeContribution} object to be used by the system
   */
  public static BytecodeContribution newItem() {
    if (inUse != null) {
      if (!inUse.my_new_contribution_required) {
        inUse.my_new_contribution_required = true;
        return inUse;
      }
    }
    return new BytecodeContribution();
  }

  /**
   * This is a listener class that receives all the events that
   * change the content of the current byte code document. This
   * covers all the editing operations.
   */
  public class BytecodeListener implements IDocumentListener {

    /**
     * The number of the final line which is removed from the document by
     * the current edit operation. Note that this field must be calculated
     * in the {@link #documentAboutToBeChanged(DocumentEvent)} method
     * as at that point the content to be removed is not removed yet.
     */
    private int my_stop_rem;

    /**
     * This field contains the string representation of the document before
     * the current change is applied.
     */
    private String my_oldcontent;

    /**
     * The current constructor does nothing.
     */
    public BytecodeListener() {
    }

    /**
     * Tries to cast the given document to {@link BytecodeDocument} with
     * appropriate message if it fails.
     *
     * @param a_doc a document to be cast
     * @return the {@link BytecodeDocument} or null in case the cast is
     *   impossible
     */
    private BytecodeDocument transformDocWithMessage(final IDocument a_doc) {
      try {
        return (BytecodeDocument) a_doc;
      } catch (ClassCastException e) {
        //This should not happen as we operate in a byte code editor
        MessageDialog.openError(my_editor.getSite().getShell(),
          GUIMessages.BYTECODE_MESSAGE_TITLE,
          GUIMessages.NOT_BYTECODE_DOCUMENT);
        return null;
      }
    }

    /**
     * This method handles the event of the change in the current
     * byte code document. This method is called before the textual
     * change is made. This method initialises the BytecodeContribution
     * object in case it has not been initialised yet.
     *
     * @param an_event the event that triggers the change, it should be
     *   the same as in {@link #documentChanged(DocumentEvent)}
     *
     * @see IDocumentListener#documentAboutToBeChanged(DocumentEvent)
     */
    public final void documentAboutToBeChanged(final DocumentEvent an_event) {
      final BytecodeDocument doc = transformDocWithMessage(an_event.fDocument);
      if (doc == null || doc.isInInit()) return;
      if (!doc.isReady()) {
        final Shell sh = my_editor.getEditorSite().getShell();
        try {
          doc.init(null, null); //this marks the document as ready
        } catch (UmbraRepresentationException e) {
          MessageDialog.openError(sh, GUIMessages.BYTECODE_MESSAGE_TITLE,
            GUIMessages.substitute(GUIMessages.REPRESENTATION_ERROR_MESSAGE,
                                   e.getProblemDescription()));
        }
      }
      try {
        my_stop_rem = doc.getLineOfOffset(an_event.getOffset() +
                                       an_event.getLength());
      } catch (BadLocationException e) {
        GUIMessages.messageWrongLocation(doc.getEditor().getSite().getShell(),
          GUIMessages.BYTECODE_MESSAGE_TITLE,
          new UmbraLocationException(true,
            an_event.getOffset() + an_event.getLength(),
            false));
      }
      my_oldcontent = doc.get();
    }


    /**
     * This method handles the update of a given fragment in the given
     * document.
     *
     * @param a_doc a document which is updated, its contents are after the
     *   update
     * @param a_start the first line of the updated region
     * @param an_oldend the last line of the updated region before the update
     * @param a_newend the last line of the updated region after the update
     */
    private void updateFragment(final BytecodeDocument a_doc,
                                final int a_start,
                                final int an_oldend,
                                final int a_newend) {
      final Shell sh = my_editor.getEditorSite().getShell();
      try {
        a_doc.updateFragment(a_start, an_oldend, a_newend);
        my_editor.getAction(BytecodeEditorContributor.REFRESH_ID).
                 setEnabled(true);
      } catch (UmbraException e) {
        MessageDialog.openError(sh,
          GUIMessages.FRAGMENT_PARSING_MESSAGE_TITLE,
          GUIMessages.INVALID_EDIT_OPERATION);
        a_doc.set(my_oldcontent);
        return;
      } catch (UmbraLocationException e) {
        GUIMessages.messageWrongLocation(sh,
          GUIMessages.FRAGMENT_PARSING_MESSAGE_TITLE, e);
        return;
      }
    }

    /**
     * This method handles the event of the change in the current
     * byte code document. This method is called after the textual
     * change is made. This method removes all the incorrect and
     * correct lines in the range that has been deleted and adds
     * all the lines in the range that has been added. Then it
     * checks if there are errors in the resulting text and
     * displays the information on the error.
     *
     * @param an_event the event that triggers the change, it should be
     *   the same as in {@link #documentAboutToBeChanged(DocumentEvent)}
     *
     * @see IDocumentListener#documentChanged(DocumentEvent)
     */
    public final void documentChanged(final DocumentEvent an_event) {
      final BytecodeDocument doc = transformDocWithMessage(an_event.fDocument);
      if (doc == null || doc.isInInit()) return;
      int stop = 0;
      int start_rem = 0;
      try {
        start_rem = doc.getLineOfOffset(an_event.getOffset());
      } catch (BadLocationException e1) {
        //This should not happen as the offsets from the event are generated
        //based on the current document
        GUIMessages.messageWrongLocation(doc.getEditor().getSite().getShell(),
          GUIMessages.BYTECODE_MESSAGE_TITLE,
          new UmbraLocationException(true, an_event.getOffset(), false));
      }
      final int insertedLen = an_event.getText().length();
      try {
        stop = doc.getLineOfOffset(an_event.getOffset() +
            insertedLen);
      } catch (BadLocationException e) {
        //This should not happen as the offsets from the event are generated
        //based on the current document
        GUIMessages.messageWrongLocation(doc.getEditor().getSite().getShell(),
          GUIMessages.BYTECODE_MESSAGE_TITLE,
          new UmbraLocationException(true,
                                     an_event.getOffset() + insertedLen,
                                     false));
      }

      updateFragment(doc, start_rem, my_stop_rem, stop);
      /*
       * FIXME (Umbra) changing field name in constant pool causes an error
       * in the following method; the source of error is probably not here
       * but in constant pool updating methods in BytecodeController
       */
      updateBML(an_event);
      displayPosition(doc, an_event.getOffset());
      if (!doc.getModel().bodyCorrect()) {
        displayError(Integer.toString(doc.getModel().getFirstError() + 1) +
                     " (Umbra)");
      } else if (!doc.annotCorrect()) {
        displayError(doc.getAnnotError() + " (BMLLib)");
      } else {
        displayCorrect();
      }
    }

    /**
     * The method updates the internal representation of the method in
     * BML structures.
     *
     * @param an_event describes the change in the document
     */
    private void updateBML(final DocumentEvent an_event) {
      try {
        ((BytecodeDocument)(an_event.fDocument)).getBmlp().onChange(an_event);
      } catch (BMLChangeException e) {
        final Shell sh = my_editor.getEditorSite().getShell();
        MessageDialog.openError(sh, GUIMessages.BYTECODE_MESSAGE_TITLE,
          GUIMessages.MALFORMED_MODIFICATION);
      }
    }

    /**
     * The method displays the information on the location of the cursor in
     * the current window.
     *
     * @param a_doc the document to display the location
     * @param an_offset the offset in the document
     */
    private void displayPosition(final BytecodeDocument a_doc,
                                 final int an_offset) {
      //TODO empty method
    }
  }

  /**
   * Returns the only contribution object that is active in the system.
   *
   * @return the active contribution object
   */
  public static BytecodeContribution inUse() {
    return inUse;
  }

  /**
   * This method marks the current object in such a way that it cannot be
   * replaced by a newly created one.
   */
  public final void survive() {
    my_new_contribution_required = false;
  }

  /**
   * Creates the GUI control associated with the byte code editor setting
   * <code>a_parent</code> as a parent and {@link SWT#BORDER} as the style.
   * It registers the current object as a data field
   * ({@link Composite#setData(Object)}) in the newly created control.
   *
   * @param a_parent a parent composite control under which the current control
   *   is registered
   * @return the freshly created control
   * @see ControlContribution#createControl(Composite)
   */
  protected final Control createControl(
                              final /*@ non_null @*/ Composite a_parent) {
    final Composite composite = new Composite(a_parent, SWT.BORDER);
    composite.setData(this);

    return composite;
  }

  /**
   * This method displays in the status line the information
   * that something is correct.
   */
  private void displayCorrect() {
    final IActionBars bars = my_editor.getEditorSite().getActionBars();
    bars.getStatusLineManager().setMessage(GUIMessages.CORRECT_CODE);
  }

  /**
   * This method displays in the status line the information
   * about an error in the indicated line.
   *
   * @param a_msg the error message
   */
  private void displayError(final String a_msg) {
    final IActionBars bars = my_editor.getEditorSite().getActionBars();
    bars.getStatusLineManager().setMessage(
      GUIMessages.substitute(GUIMessages.INCORRECT_CODE,  a_msg));
  }

  /**
   * This method displays in the status line the information
   * about the cursor position inside the BML document.
   *
   * @param a_doc the document to print the position for
   * @param an_offset the offset within the document to report
   */
  private void displayPosition(final BytecodeDocument a_doc,
                               final int an_offset) {
    final IActionBars bars = my_editor.getEditorSite().getActionBars();
    int lno;
  // TODO probably this must be done as in
  //http://www.koders.com/java/fid0EFC07132C90D211D4D2868ECDB3C6BA3A025AB5.aspx
    try {
      lno = a_doc.getLineOfOffset(an_offset);
      final int chpos = an_offset - a_doc.getLineOffset(lno) + 1;
      bars.getStatusLineManager().setMessage("" + lno + " : " + chpos);
    } catch (BadLocationException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  }

  /**
   * This method adds to the document <code>a_doc</code> a listener
   * which keeps track of all the document modifications.
   *
   * @param a_doc a document the modifications of which will be notified
   *   by the listener
   */
  public final void addListener(final IDocument a_doc) {
    final BytecodeDocument doc = (BytecodeDocument) a_doc;
    if (doc.isListenerAdded()) {
      final BytecodeListener listener = new BytecodeListener();
      a_doc.addDocumentListener(listener);
    }
  }

  /**
   * This method sets the byte code editor for which the
   * byte code contribution works. Currently, it does nothing as the
   * editor is not used internally.
   *
   * @param a_target_editor the byte code editor for which the action will be
   *    executed
   */
  public void setActiveEditor(final IEditorPart a_target_editor) {
    my_editor = (BytecodeEditor)a_target_editor;
  }

}
