package prover.gui.editor;

import java.util.LinkedList;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.presentation.PresentationReconciler;


public class BasicPresentationReconciler extends PresentationReconciler{
	private IDocument document;
	private ITextViewer viewer;
	private FindReplaceDocumentAdapter fda;
	private LimitRuleScanner crs;
	IDocumentListener list;
	public BasicPresentationReconciler(LimitRuleScanner scan) {
		super();
		crs = scan;
	}
	/**
	 * Informs all registered damagers about the document on which they will work.
	 *
	 * @param document the document on which to work
	 */
	protected void setDocumentToDamagers(IDocument document) {
		if(this.document != null) {
			this.document.removeDocumentListener(list);
		}
		this.document = document;
		list = new IDocumentListener() {
			LinkedList li = new LinkedList();
			boolean flag = false;	
			public void documentAboutToBeChanged(DocumentEvent event) {
				
				IDocument doc = event.getDocument();
				
				DocumentEvent ev;
				
				if(flag || (event.getOffset() > (crs.getLimit() - 1))) {
					flag = false;
					return;
				}
				flag = true;
				try {
					ev = new DocumentEvent(doc, event.getOffset(),
							event.getText().length(), doc.get(event.getOffset(),
									event.getLength()));
					li.add(ev);
				} catch (BadLocationException e) {}
				
				
			}
			
			public void documentChanged(DocumentEvent event) {
				if(li.size() > 0) {
					DocumentEvent de = (DocumentEvent)li.removeFirst();
					
					try {
						de.getDocument().replace(de.getOffset(), de.getLength(), de.getText());
					} catch (BadLocationException e) {
					}
					
				}
			}
			
		};
		document.addDocumentListener(list);
		fda = new FindReplaceDocumentAdapter(document);
		super.setDocumentToDamagers(document);
		
	}
	public void everythingHasChanged(int beg, int end) {
		if(end >= document.getLength()) {
			end = document.getLength()-1;
		}
		if(beg > end) {
			beg = end;
		}
		if(beg < 0) {
			beg = 0;
		}
		
		TextPresentation p= createPresentation(new Region(beg, end), document);
		if (p != null)
			viewer.changeTextPresentation(p, false);
		viewer.revealRange(crs.getLimit() - 1, 1);
		viewer.setSelectedRange(crs.getLimit(), 0);
	}
	public void everythingHasChanged() {
		TextPresentation p= createPresentation(new Region(0, document.getLength()), document);
		if (p != null)
			viewer.changeTextPresentation(p, false);
		viewer.revealRange(crs.getLimit() - 1, 1);
	}
	public IDocument getDocument() {
		return document;
	}
	public void install(ITextViewer v) {
		viewer = v;
		super.install(v);
	}
	public FindReplaceDocumentAdapter getFinder() {
		return fda;
	}

}
