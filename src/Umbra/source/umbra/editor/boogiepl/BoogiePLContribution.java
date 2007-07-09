/*
 * Created on 2005-05-03
 *
 */
package umbra.editor.boogiepl;

import org.eclipse.jface.action.ControlContribution;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IEditorPart;

// import umbra.instructions.boogiepl.BoogiePLController;

/**
 * TODO.
 *
 * @author Samuel Willimann (wsamuel@student.ethz.ch)
 * @version a-01
 */
public class BoogiePLContribution extends ControlContribution {

  /**
   * TODO.
   */
  private static final RGB WIDGET_FOREGROUND_COLOR = new RGB(255, 255, 0);

  /**
   * TODO.
   */
  private static final int WIDGET_TEXT_STYLE = 1;

  /**
   * TODO.
   */
  private static final int WIDGET_TEXT_HEIGHT = 8;

  /**
   * TODO.
   */
  private static final int WIDGET_HEIGHT = 15;

  /**
   * TODO.
   */
  private static final int WIDGET_WIDTH = 120;

  /**
   * TODO.
   */
  private static BoogiePLContribution inUse;

  /**
   * TODO.
   */
  private boolean needNew = true;

  /**
   * The current BoogiePL editor for which the contribution works.
   */
  private IEditorPart my_editor;
  /**
   * TODO.
   */
  private Label labelText;

  /**
   * TODO
   */
  // private BoogiePLController bcc;
  /**
   * TODO.
   */
  private boolean ready;

  /**
   * TODO.
   */
  protected BoogiePLContribution() {
    super("BoogiePL");
    inUse = this;
  }

  /**
   * TODO.
   * @param a_doc TODO
   * @throws BadLocationException TODO
   */
  private void init(final IDocument a_doc) throws BadLocationException {
    /*
    bcc = new BoogiePLController();
    bcc.init(doc);
    if (modTable) {
      bcc.setModified(modified);
      modTable = false;
    }
    bcc.checkAllLines(0, doc.getNumberOfLines() - 2);
    ready = true;
    return;
    */
  }

  /**
   * TODO.
   */
  public class BoogiePLListener implements IDocumentListener {

    /**
     * TODO.
     */
    int startRem = -1, stopRem = -1;

    /**
     * TODO.
     */
    public BoogiePLListener() {
    }

    /**
     * TODO.
     * @param event TODO
     * @see IDocumentListener#documentAboutToBeChanged(DocumentEvent)
     */
    public final void documentAboutToBeChanged(final DocumentEvent event) {
      if (!ready)
        try {
          init(event.fDocument);
        } catch (BadLocationException e1) {
          // TODO Auto-generated catch block
          e1.printStackTrace();
        }
      try {
        startRem = event.fDocument.getLineOfOffset(event.getOffset());
        final int len = event.fLength;
        stopRem = event.fDocument.getLineOfOffset(event.getOffset() + len);
        // bcc.removeIncorrects(startRem, stopRem);
      } catch (BadLocationException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }

    /**
     * TODO.
     * @param event TODO
     * @see IDocumentListener#documentChanged(DocumentEvent)
     */
    public final void documentChanged(final DocumentEvent event) {
      //int start = 0, stop = 0;
      try {
        //start =
        event.fDocument.getLineOfOffset(event.getOffset());
        final int len = event.getText().length();
        //stop =
        event.fDocument.getLineOfOffset(event.getOffset() + len);

      } catch (BadLocationException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
      /*
      bcc.addAllLines(event.fDocument, startRem, stopRem, start, stop);
      startRem = -1;
      stopRem = -1;
      bcc.checkAllLines(start, stop);
      if (!bcc.allCorrect())
        displayError(bcc.getFirstError());
      else displayCorrect();
      */
    }

  }

  /**
   * TODO.
   * @return TODO
   */
  public static BoogiePLContribution inUse() {
    return inUse;
  }

  /**
   * TODO.
   * @return TODO
   */
  public static BoogiePLContribution newItem() {
    if (inUse != null) {
      if (!inUse.needNew) {
        inUse.needNew = true;
        return inUse;
      }
    }
    return new BoogiePLContribution();
  }

  /**
   * TODO.
   */
  public final void survive() {
    needNew = false;
  }

  /**
   * Creates the GUI control associated with the BoogiePL editor by setting
   * <code>a_parent</code> as a parent and {@ref SWT#BORDER} as the style.
   * It registers the current object as a data field
   * ({@see Composite#setData(Object)}) in the newly created control. Next,
   * the method adds a label of the size {@ref #WIDGET_WIDTH},
   * {@ref #WIDGET_HEIGHT}, font "Arial" of the height
   * {@ref #WIDGET_TEXT_HEIGHT} and style {@ref #WIDGET_TEXT_STYLE}. The text
   * is typed using the color {@ref #WIDGET_FOREGROUND_COLOR}.
   *
   * @param a_parent a parent composite control under which the current control
   *                 is registered
   * @return the freshly created control
   * @see ControlContribution#createControl(Composite)
   */
  protected final Control createControl(final Composite a_parent) {
    final Composite composite = new Composite(a_parent, SWT.BORDER);
    composite.setData(this);

    labelText = new Label(composite, SWT.NONE);
    labelText.setSize(WIDGET_WIDTH, WIDGET_HEIGHT);
    labelText.setFont(new Font(null, "Arial", WIDGET_TEXT_HEIGHT,
                                              WIDGET_TEXT_STYLE));
    labelText.setForeground(new Color(null, WIDGET_FOREGROUND_COLOR));
    return composite;
  }

  /**
   * used for debugging purposes
   *
  private void displayCorrect() {
    labelText.setBackground(new Color(null, new RGB(0, 128, 0)));
    labelText.setText("Correct");
  } */

  /**
   * used for debugging purposes
   *
  private void displayError(int line) {
    labelText.setBackground(new Color(null, new RGB(255, 128, 0)));
    labelText.setText("Error detected: " + line);
  }*/

  /**
   * TODO.
   * @param a_doc TODO
   */
  public final void addListener(final IDocument a_doc) {
    final BoogiePLListener listener = new BoogiePLListener();
    a_doc.addDocumentListener(listener);
  }

  /**
   * @param an_editor TODO
   */
  public final void setActiveEditor(final IEditorPart an_editor) {
    my_editor = an_editor;
  }

  /**
   * @return the current BoogiePL editor for which the contribution works.
   */
  public final IEditorPart getActiveEditor() {
    return my_editor;
  }

  /**
   * TODO.
   */
  public final void reinit() {
    ready = false;
  }

  /**
   * TODO.
   * @return TODO
   */
  public final boolean[] getModified() {
    return null; // return bcc.getModified();
  }

  /**
   * The method currently does nothing.
   *
   * @param the_modified a table which indicates which methods are modified
   */
  public void setModTable(final boolean[] the_modified) {
  }

  /**
   * TODO.
   * @return TODO
   */
  public final String[] getCommentTab() {
    return null; // return bcc.getComments();
  }

  /**
   * TODO.
   * @return TODO
   */
  public final String[] getInterlineTab() {
    return null; // return bcc.getInterline();
  }
}
