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
 * TODO
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
   * TODO
   */
  private boolean needNew = true;
  /**
   * TODO
   */
  private IEditorPart activeEditor;
  /**
   * TODO
   */
  private Label labelText;
  /**
   * TODO
   */
  private static BoogiePLContribution inUse;
  /**
   * TODO
   */
  // private BoogiePLController bcc;
  /**
   * TODO
   */
  private boolean ready = false;

  /**
   * TODO
   */
  protected BoogiePLContribution() {
    super("BoogiePL");
    inUse = this;
  }

  /**
   * TODO
   */
  private void init(final IDocument doc) throws BadLocationException
  {
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
   * TODO
   */
  public class BoogiePLListener implements IDocumentListener {

    /**
     * TODO
     */
    int startRem = -1, stopRem = -1;

    /**
     * TODO
     */
    public BoogiePLListener() {
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.IDocumentListener#documentAboutToBeChanged(org.eclipse.jface.text.DocumentEvent)
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

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.IDocumentListener#documentChanged(org.eclipse.jface.text.DocumentEvent)
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
   * TODO
   */
  public static BoogiePLContribution inUse() {
    return inUse;
  }

  /**
   * TODO
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
   * TODO
   */
  public final void survive() {
    needNew = false;
  }

  /**
   * TODO
   * @param parent
   * @return
   * @see org.eclipse.jface.action.ControlContribution#createControl(org.eclipse.swt.widgets.Composite)
   */
  protected final Control createControl(final Composite parent) {
    final Composite composite = new Composite(parent, SWT.BORDER);
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
   * TODO
   */
  public final void addListener(final IDocument document) {
    final BoogiePLListener listener = new BoogiePLListener();
    document.addDocumentListener(listener);
  }

  /**
   * @param editor
   */
  public final void setActiveEditor(final IEditorPart editor) {
    activeEditor = editor;
  }

  /**
   * @param editor
   */
  public final IEditorPart getActiveEditor() {
    return activeEditor;
  }

  /**
   * TODO
   */
  public final void reinit() {
    ready = false;
  }

  /**
   * TODO
   */
  public final boolean[] getModified() {
    return null; // return bcc.getModified();
  }

  /**
   * TODO
   */
  public void setModTable(final boolean[] modified) {
  }

  /**
   * TODO
   */
  public final String[] getCommentTab() {
    return null; // return bcc.getComments();
  }

  /**
   * TODO
   */
  public final String[] getInterlineTab() {
    return null; // return bcc.getInterline();
  }
}
