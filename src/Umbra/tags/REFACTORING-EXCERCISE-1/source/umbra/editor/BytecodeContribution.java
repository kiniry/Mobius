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
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;

import umbra.UmbraPlugin;
import umbra.instructions.BytecodeController;

/**
 * This class represents a GUI element that is contributed to the
 * eclipse GUI by the bytecode editor.
 *
 * change performed in a bytecode editor.
 * TODO more detailed description is needed
 *
 * @author Wojciech Wąs  (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeContribution extends ControlContribution {

  /**
   * TODO. what does the constant mean?
   */
  private static final int CHECK_ALL_LINES_DECREMENT = 2;

  /**
   * TODO.
   */
  private static BytecodeContribution inUse;

  /**
   * TODO.
   */
  private boolean my_need_new_flag = true;

  /**
   * TODO.
   */
  private BytecodeController my_bcc;

  /**
   * TODO.
   */
  private boolean my_ready_flag;

  /**
   * TODO.
   */
  private boolean my_mod_table_flag; //@ initially false;

  /**
   * This array keeps track of which methods in the class edited by the
   * bytecode editor are modified. It contains <code>true</code> on i-th
   * position when the i-th method is modified.
   *
   * TODO it's not completely true, the my_modified in my_bcc is the actual
   * point
   */
  private boolean[] my_modified;

  /**
   * The manager that initialises all the actions within the
   * bytecode plugin.
   */
  private BytecodeEditorContributor my_editor_cntrbtr;

  /* *
   * The current bytecode editor for which the contribution works.
   */
  //private IEditorPart my_editor; it's never read

  /**
   * TODO.
   */
  protected BytecodeContribution() {
    super("Bytecode");
    inUse = this;
  }

  /**
   * This method initialises the internal structures of the bytecode
   * contribution. In particular it initialises the object that
   * manages the BCEL operations and enables the relevant actions
   * in the Umbra plugin bytecode contributor.
   *
   * TODO what's my_mod_table_flag
   * @param a_doc TODO
   */
  private void init(final IDocument a_doc) {
    my_bcc = new BytecodeController();
    my_bcc.init(a_doc);
    if (my_mod_table_flag) {
      my_bcc.setModified(my_modified);
      my_mod_table_flag = false;
    }
    //TODO why we decrease here by CHECK_ALL_LINES_DECREMENT?
    my_bcc.checkAllLines(0,
                         a_doc.getNumberOfLines() - CHECK_ALL_LINES_DECREMENT);
    my_ready_flag = true;
    my_editor_cntrbtr.getRefreshAction().setEnabled(true);
  }

  /**
   * This is a listener class that receives all the events that
   * change the content of the current bytecode document.
   */
  public class BytecodeListener implements IDocumentListener {

    /**
     * Data passed from documentAboutToBeChanged to documentChanged.
     * Should be null if no event is currently being processed.
     */
    private DocumentEvent my_current_event; //@ initially null;

    /**
     * TODO.
     */
    private int my_end_line;

    /**
     * The current constructor does nothing.
     */
    public BytecodeListener() {
    }


    /**
     * This method handles the event of the change in the current
     * bytecode document. This method is called before the textual
     * change is made. This method initialises the BytecodeContribution
     * object in case it has not been initialised yet.
     *
     * @param an_event the event that triggers the change, it should be
     * the same as in {@ref #documentChanged(DocumentEvent)}
     *
     * @see IDocumentListener#documentAboutToBeChanged(DocumentEvent)
     */
    public final void documentAboutToBeChanged(final DocumentEvent an_event) {
      if (!my_ready_flag)
        init(an_event.fDocument); //this marks my_ready_flag as true
      UmbraPlugin.messagelog("documentAboutToBeChanged " +
                             an_event.getText());
      UmbraPlugin.messagelog("documentAboutToBeChanged " +
                             an_event.getModificationStamp());
      UmbraPlugin.messagelog("documentAboutToBeChanged " +
                             an_event.getOffset());
      UmbraPlugin.messagelog("documentAboutToBeChanged " +
                             an_event.getLength());
      UmbraPlugin.messagelog("documentAboutToBeChanged " +
                             an_event.getDocument().hashCode());
      UmbraPlugin.LOG.flush();
      my_current_event = an_event;

      try {
        my_end_line = an_event.fDocument.getLineOfOffset(
              an_event.getOffset() + an_event.getLength());
      } catch (BadLocationException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }

    /**
     * This method handles the event of the change in the current
     * bytecode document. This method is called after the textual
     * change is made. This method removes all the incorrect and
     * correct lines in the range that has been deleted and adds
     * all the lines in the range that has been added. Then it
     * checks if there are errors in the resulting text and
     * displays the information on the error.
     *
     * @param an_event the event that triggers the change, it should be
     * the same as in {@ref #documentAboutToBeChanged(DocumentEvent)}
     *
     * @see IDocumentListener#documentChanged(DocumentEvent)
     */
    public final void documentChanged(final DocumentEvent an_event) {
      UmbraPlugin.messagelog("documentChanged " + an_event.getText());
      UmbraPlugin.LOG.flush();
      int stop = 0;
      int start_rem = 0, stop_rem = 0;
      try {
        start_rem = an_event.fDocument.getLineOfOffset(an_event.getOffset());
        final int insertedLen = an_event.getText().length();
        stop = an_event.fDocument.getLineOfOffset(an_event.getOffset() +
            insertedLen);
        if (an_event == my_current_event) {
          stop_rem = my_end_line;
        } else {
          throw new RuntimeException("documentChanged event does not match " +
                                     "documentAboutToBeChanged event");
        }
        my_current_event = null;
      } catch (BadLocationException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
      my_bcc.removeIncorrects(start_rem, stop_rem);
      my_bcc.addAllLines(an_event.fDocument, start_rem, stop_rem, stop);
      my_bcc.checkAllLines(start_rem, stop);
      if (!my_bcc.allCorrect())
        displayError(an_event.fDocument, my_bcc.getFirstError());
      else displayCorrect(an_event.fDocument);
    }

  }

  /**
   * TODO.
   * @return TODO
   */
  public static BytecodeContribution inUse() {
    return inUse;
  }

  /**
   * TODO.
   * @return TODO
   */
  public static BytecodeContribution newItem() {
    if (inUse != null) {
      if (!inUse.my_need_new_flag) {
        inUse.my_need_new_flag = true;
        return inUse;
      }
    }
    return new BytecodeContribution();
  }

  /**
   * TODO.
   */
  public final void survive() {
    my_need_new_flag = false;
  }

  /**
   * Creates the GUI control associated with the bytecode editor setting
   * <code>a_parent</code> as a parent and {@ref SWT#BORDER} as the style.
   * It registers the current object as a data field
   * ({@ref Composite#setData(Object)}) in the newly created control.
   *
   * @param a_parent a parent composite control under which the current control
   *                 is registered
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
   *
   * @param a_doc the status line is extracted from
   */
  private void displayCorrect(final IDocument a_doc) {
    final BytecodeEditor editor = ((BytecodeDocument)a_doc).getEditor();
    final IActionBars bars = editor.getEditorSite().getActionBars();
    bars.getStatusLineManager().setMessage("Correct");
  }

  /**
   * This method displays in the status line the information
   * about an error in the indicated line.
   *
   * @param a_doc the status line is extracted from
   * @param a_line the number of the line with the error
   */
  private void displayError(final IDocument a_doc, final int a_line) {
    final BytecodeEditor editor = ((BytecodeDocument)a_doc).getEditor();
    final IActionBars bars = editor.getEditorSite().getActionBars();
    bars.getStatusLineManager().setMessage("Error detected: " + a_line);
  }

  /**
   * This method adds to the document in the parameter a listener
   * which keeps track of all the document modifications.
   *
   * @param a_doc the modifications of which will be notified
   * by the listener
   */
  public final void addListener(final IDocument a_doc) {
    final BytecodeDocument doc = (BytecodeDocument) a_doc;
    if (doc.isListenerAdded()) {
      final BytecodeListener listener = new BytecodeListener();
      a_doc.addDocumentListener(listener);
    }
  }

  /**
   * This method sets the bytecode editor for which the
   * bytecode contribution works. Currently, it does nothing as the
   * editor is not used internally.
   *
   * @param a_target_editor the bytecode editor for which the action will be
   *    executed
   */
  public void setActiveEditor(final IEditorPart a_target_editor) {
    //my_editor = a_target_editor; it's never read
  }

  /**
   * TODO.
   */
  public final void reinit() {
    my_ready_flag = false;
  }

  /**
   * @return boolean array, an entry is <code>true</code> whenever
   * the corresponding method is modified by the bytecode editor
   */
  public final boolean[] getModified() {
    return my_bcc.getModified();
  }

  /**
   * TODO.
   * @param the_modified a table which indicates which methods are modified
   */
  public final void setModTable(final boolean[] the_modified) {
    this.my_modified = the_modified;
    my_mod_table_flag = true;
  }

  /**
   * @return a {@ref String} table which represents bytecode comments
   * associated with subsequent lines of the bytecode file associated with
   * the current editor
   */
  public final String[] getCommentTab() {
    return my_bcc.getComments();
  }

  /**
   * TODO.
   * @return TODO
   */
  public final String[] getInterlineTab() {
    return my_bcc.getInterline();
  }

  /**
   * TODO.
   * @param a_contributor TODO
   */
  public final void addEditorContributor(
                          final BytecodeEditorContributor a_contributor) {
    my_editor_cntrbtr = a_contributor;
  }
}
