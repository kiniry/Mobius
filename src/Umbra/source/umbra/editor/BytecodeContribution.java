/*
 * Created on 2005-05-03
 *
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
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IEditorPart;

import umbra.instructions.BytecodeController;

/**
 * This class represents a change performed in a bytecode editor.
 * TODO more detailed description is needed
 * 
 * @author Wojtek Was
 */
public class BytecodeContribution extends ControlContribution { 
	
	/**
	 * TODO
	 */
	private boolean needNew = true;
	/**
	 * TODO
	 */
	private Label labelText;
	/**
	 * TODO
	 */
	private static BytecodeContribution inUse;
	/**
	 * TODO
	 */
	private BytecodeController bcc;	
	/**
	 * TODO
	 */
	private boolean ready = false;
	/**
	 * TODO
	 */
	private boolean modTable = false;
	
	/**
	 * TODO
	 */
	private boolean[] modified;
	
	/**
	 * TODO
	 */
	private BytecodeEditorContributor editorContributor;
	
	/**
	 * TODO
	 */
	private void init(IDocument doc) throws BadLocationException
	{
		bcc = new BytecodeController();
		bcc.init(doc);
		if (modTable) {
			bcc.setModified(modified);
			modTable = false;
		}
		bcc.checkAllLines(0, doc.getNumberOfLines() - 2);
		ready = true;
		editorContributor.getRefreshAction().setEnabled(true);
		return;
	}
	
	/**
	 * TODO
	 */
	public class BytecodeListener implements IDocumentListener {
		
		/**
		 * TODO
		 */
		int startRem = -1, stopRem = -1;
		
		/**
		 * TODO
		 */
		public BytecodeListener() {
		}

		/* (non-Javadoc)
		 * @see org.eclipse.jface.text.IDocumentListener#documentAboutToBeChanged(org.eclipse.jface.text.DocumentEvent)
		 */
		public void documentAboutToBeChanged(DocumentEvent event) {
			if (!ready)
				try {
					init(event.fDocument);
				} catch (BadLocationException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
			try {
				startRem = event.fDocument.getLineOfOffset(event.getOffset());
				int len = event.fLength;
				stopRem = event.fDocument.getLineOfOffset(event.getOffset() + len);
				bcc.removeIncorrects(startRem, stopRem);
			} catch (BadLocationException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		/* (non-Javadoc)
		 * @see org.eclipse.jface.text.IDocumentListener#documentChanged(org.eclipse.jface.text.DocumentEvent)
		 */
		public void documentChanged(DocumentEvent event) {
			int start = 0, stop = 0;
			try {
				start = event.fDocument.getLineOfOffset(event.getOffset());
				int len = event.getText().length();
				stop = event.fDocument.getLineOfOffset(event.getOffset() + len);
			} catch (BadLocationException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			bcc.addAllLines(event.fDocument, startRem, stopRem, start, stop);
			startRem = -1;
			stopRem = -1;
			bcc.removeIncorrects(start, stop);
			bcc.checkAllLines(start, stop);
			if (!bcc.allCorrect()) 
				displayError(bcc.getFirstError());
			else displayCorrect();
		}
		
	}
	
	/**
	 * TODO
	 */
	protected BytecodeContribution() {
		super("Bytecode");
		inUse = this;
	}
	
	/**
	 * TODO
	 */
	public static BytecodeContribution inUse() {
		return inUse;
	}
	
	/**
	 * TODO
	 */
	public static BytecodeContribution newItem() {
		if (inUse != null) {
			if (!inUse.needNew) {
				inUse.needNew = true;	
				return inUse;
			}	
		}
		return new BytecodeContribution();
	}
	
	/**
	 * TODO
	 */
	public void survive() {
		needNew = false;
	}
	
	/**
	 * TODO
	 */
	protected Control createControl(Composite parent) {
		Composite composite = new Composite(parent, SWT.BORDER);
		composite.setData(this);

		labelText = new Label(composite, SWT.NONE);
		labelText.setSize(220, 15);
		//labelText.setFont(new Font(null, "Times", 8, 1));
		//labelText.setForeground(new Color(null, new RGB(255, 255, 0)));
		return composite;
	}
	
	/**
	 * This method displays in the status label the information
	 * that something is correct.
	 */
	private void displayCorrect() {
		labelText.setText("Correct");
		System.out.println("Correct");
	}
	
	/**
	 * This method displays in the status label the information
	 * about an error in the indicated line.
	 * 
	 * @param line the number of the line with the error
	 */
	private void displayError(int line) {
		//labelText.setBackground(new Color(null, new RGB(255, 128, 0)));
		labelText.setText("Error detected: " + line);
		System.out.println("Error detected: " + line);
	}

	/**
	 * TODO
	 */
	public void addListener(IDocument document) {
		BytecodeListener listener = new BytecodeListener();
		document.addDocumentListener(listener);
	}

	/**
	 * @param editor
	 */
	public void setActiveEditor(IEditorPart editor) {
	}
	
	/**
	 * TODO
	 */
	public void reinit() {
		ready = false;
	}
	
	/**
	 * TODO
	 */
	public boolean[] getModified() {
		return bcc.getModified();
	}
	
	/**
	 * TODO
	 */
	public void setModTable(boolean[] modified) {
		this.modified = modified;
		modTable = true;
	}

	/**
	 * TODO
	 */
	public String[] getCommentTab() {
		return bcc.getComments();
	}
	
	/**
	 * TODO
	 */
	public String[] getInterlineTab() {
		return bcc.getInterline();
	}

	/**
	 * TODO
	 * @param contributor
	 */
	public void addEditorContributor(BytecodeEditorContributor contributor) {
		editorContributor = contributor;
	}
}
