package mobius.prover.gui.editor;

import java.util.Stack;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.presentation.PresentationReconciler;

/**
 * A presentation reconciler to avoid editing of a text below a limit
 * defined by a scanner associated with it.
 *
 * @author J. Charles (julien.charles@inria.fr)
 */
public class BasicPresentationReconciler extends PresentationReconciler {
  /** the document associated with the reconciler. */
  private IDocument fDoc;
  /** the viewer associated with the reconciler. */
  private ITextViewer fViewer;
  /** the scanner uset to highlight a part of the text. */
  private LimitRuleScanner fScanner;
  /** the listener to listen to the events associated with the document. */
  private IDocumentListener fListener;
  
  /**
   * Create a presentation reconciler associated with a scanner. 
   * @param scan The scanner of the presentation reconciler
   */
  public BasicPresentationReconciler(final LimitRuleScanner scan) {
    super();
    fScanner = scan;
  }
  
  
  /** {@inheritDoc} */
  @Override
  protected void setDocumentToDamagers(final IDocument doc) {
    if (fDoc != null && (fListener != null)) {
      fDoc.removeDocumentListener(fListener);
    }
    fDoc = doc;
    fListener = new DocumentListener();
    doc.addDocumentListener(fListener);
    super.setDocumentToDamagers(doc);
  }
  
  
  
  /**
   * Update the presentation of the viewer associated
   * with the presentation reconciler, but only a part of it
   * within a specified range.
   * @param b The beginning of the part to update.
   * @param e The end of the part to update.
   */
  public void everythingHasChanged(final int b, final int e) {
    int beg = b;
    int end = e;
    if (end >= fDoc.getLength()) {
      end = fDoc.getLength() - 1;
    }
    if (beg > end) {
      beg = end;
    }
    if (beg < 0) {
      beg = 0;
    }
    
    final TextPresentation p = createPresentation(new Region(beg, end), fDoc);
    if (p != null) {
      fViewer.changeTextPresentation(p, false);
    }
    //fViewer.revealRange(fScanner.getLimit() - 1, 1);
    int offset = 0;
    try {
      offset = fDoc.getLineOffset(fDoc.getNumberOfLines(0, fScanner.getLimit()));
    } 
    catch (BadLocationException exc) {
      // TODO Auto-generated catch block
      exc.printStackTrace();
    }

    fViewer.revealRange(offset, 1);
    if (fViewer.isEditable()) {
      fViewer.setSelectedRange(offset, 0);
    }
    //fViewer.setSelectedRange(fScanner.getLimit(), 0);
  }
  
  
  /**
   * Update the presentation of the viewer associated with 
   * the presentation reconciler.
   */
  public void everythingHasChanged() {
    final TextPresentation p = createPresentation(new Region(0, fDoc.getLength()), fDoc);
    if (p != null) {
      fViewer.changeTextPresentation(p, false);
    }
    fViewer.revealRange(fScanner.getLimit() - 1, 1);
  }
  
  /**
   * Return the current document associated with this presentation reconciler.
   * @return A document or <code>null</code>
   */
  public IDocument getDocument() {
    return fDoc;
  }
  
  public ITextViewer getViewer() {
    return fViewer;
  }
  
  /** {@inheritDoc} */
  @Override
  public void install(final ITextViewer v) {
    fViewer = v;
    super.install(v);
  }
  
  /**
   * A class used to avoid the change of a document if it is below a 
   * limit given by the scanner.
  
   */
  private class DocumentListener implements IDocumentListener {
    /** the list of events to undo. */
    private Stack<DocumentEvent> fUpcoming = new Stack<DocumentEvent>();
    /** a flag to avoid recursive call. */
    private boolean fFlag;
    
    /** {@inheritDoc} */
    @Override
    public void documentAboutToBeChanged(final DocumentEvent event) {
      final IDocument doc = event.getDocument();
      DocumentEvent ev;
      if (fFlag || (event.getOffset() > (fScanner.getLimit() - 1))) {
        fFlag = false;
        return;
      }
      fFlag = true;
      try {
        ev = new DocumentEvent(doc, event.getOffset(),
            event.getText().length(), doc.get(event.getOffset(),
                event.getLength()));
        fUpcoming.push(ev);
      } 
      catch (BadLocationException e) {
        
      }
    }
    
    /** {@inheritDoc} */
    @Override
    public void documentChanged(final DocumentEvent event) {
      if (fUpcoming.size() > 0) {
        final DocumentEvent de = (DocumentEvent)fUpcoming.pop();  
        try {
          de.getDocument().replace(de.getOffset(), de.getLength(), de.getText());
        } 
        catch (BadLocationException e) {
        }
      }
    }  
  }
}
