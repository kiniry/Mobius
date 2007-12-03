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
 */
public class BasicPresentationReconciler extends PresentationReconciler {
	/** the document associated with the reconciler */
	private IDocument fDoc;
	/** the viewer associated with the reconciler */
	private ITextViewer fViewer;
	/** the scanner uset to highlight a part of the text */
	private LimitRuleScanner fScanner;
	/** the listener to listen to the events associated with the document */
	private IDocumentListener fListener;
	
	/**
	 * Create a presentation reconciler associated with a scanner. 
	 * @param scan The scanner of the presentation reconciler
	 */
	public BasicPresentationReconciler(LimitRuleScanner scan) {
		super();
		fScanner = scan;
	}
	
	
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.jface.text.presentation.PresentationReconciler#setDocumentToDamagers(org.eclipse.jface.text.IDocument)
	 */
	protected void setDocumentToDamagers(IDocument doc) {
		if(fDoc != null && (fListener != null)) {
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
	 * @param beg The beginning of the part to update.
	 * @param end The end of the part to update.
	 */
	public void everythingHasChanged(int beg, int end) {
		if(end >= fDoc.getLength()) {
			end = fDoc.getLength()-1;
		}
		if(beg > end) {
			beg = end;
		}
		if(beg < 0) {
			beg = 0;
		}
		
		TextPresentation p= createPresentation(new Region(beg, end), fDoc);
		if (p != null)
			fViewer.changeTextPresentation(p, false);
		//fViewer.revealRange(fScanner.getLimit() - 1, 1);
		int offset = 0;
		try {
			offset = fDoc.getLineOffset(fDoc.getNumberOfLines(0, fScanner.getLimit()));
		} catch (BadLocationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		fViewer.revealRange(offset, 1);
		if(fViewer.isEditable()) {
			fViewer.setSelectedRange(offset,0);
		}
		//fViewer.setSelectedRange(fScanner.getLimit(), 0);
	}
	
	
	/**
	 * Update the presentation of the viewer associated with 
	 * the presentation reconciler.
	 */
	public void everythingHasChanged() {
		TextPresentation p= createPresentation(new Region(0, fDoc.getLength()), fDoc);
		if (p != null)
			fViewer.changeTextPresentation(p, false);
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
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.jface.text.presentation.IPresentationReconciler#install(org.eclipse.jface.text.ITextViewer)
	 */
	public void install(ITextViewer v) {
		fViewer = v;
		super.install(v);
	}
	
	/**
	 * A class used to avoid the change of a document if it is below a 
	 * limit given by the scanner.
	
	 */
	private class DocumentListener implements IDocumentListener {
		/** the list of events to undo */
		private Stack fUpcoming = new Stack();
		/** a flag to avoid recursive call */
		private boolean flag = false;
		
		/*
		 *  (non-Javadoc)
		 * @see org.eclipse.jface.text.IDocumentListener#documentAboutToBeChanged(org.eclipse.jface.text.DocumentEvent)
		 */
		public void documentAboutToBeChanged(DocumentEvent event) {
			IDocument doc = event.getDocument();
			DocumentEvent ev;
			if(flag || (event.getOffset() > (fScanner.getLimit() - 1))) {
				flag = false;
				return;
			}
			flag = true;
			try {
				ev = new DocumentEvent(doc, event.getOffset(),
						event.getText().length(), doc.get(event.getOffset(),
								event.getLength()));
				fUpcoming.push(ev);
			} catch (BadLocationException e) {}
		}
		
		/*
		 *  (non-Javadoc)
		 * @see org.eclipse.jface.text.IDocumentListener#documentChanged(org.eclipse.jface.text.DocumentEvent)
		 */
		public void documentChanged(DocumentEvent event) {
			if(fUpcoming.size() > 0) {
				DocumentEvent de = (DocumentEvent)fUpcoming.pop();	
				try {
					de.getDocument().replace(de.getOffset(), de.getLength(), de.getText());
				} catch (BadLocationException e) {
				}
			}
		}	
	}
}
