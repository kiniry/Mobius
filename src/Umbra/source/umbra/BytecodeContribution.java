/*
 * Created on 2005-05-03
 *
 */
package umbra;

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

import umbra.instructions.BytecodeController;

/**
 * @author Wojtek W¹s
 */
public class BytecodeContribution extends ControlContribution { 
	
	private int num = 0;
	private boolean needNew = true;
	private IEditorPart activeEditor;
	private Label labelNum, labelOff, labelText;
	private static BytecodeContribution inUse;
	private BytecodeController bcc;	
	private boolean ready = false;
	private boolean modTable = false;
	private boolean[] modified;
	
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
		return;
	}
	
	public class BytecodeListener implements IDocumentListener {
		
		int startRem = -1, stopRem = -1;
		
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
			bcc.checkAllLines(start, stop);
			if (!bcc.allCorrect()) 
				displayError(bcc.getFirstError());
			else displayCorrect();
		}
		
	}
	
	protected BytecodeContribution() {
		super("Bytecode");
		inUse = this;
	}
	
	public static BytecodeContribution inUse() {
		return inUse;
	}
	
	public static BytecodeContribution newItem() {
		if (inUse != null) {
			if (!inUse.needNew) {
				inUse.needNew = true;	
				return inUse;
			}	
		}
		return new BytecodeContribution();
	}
	
	public void survive() {
		needNew = false;
	}
	
	protected Control createControl(Composite parent) {
		Composite composite = new Composite(parent, SWT.BORDER);
		composite.setData(this);

		labelText = new Label(composite, SWT.NONE);
		labelText.setSize(120, 15);
		labelText.setFont(new Font(null, "Arial", 8, 1));
		labelText.setForeground(new Color(null, new RGB(255, 255, 0)));
		return composite;
	}
	
	private void displayCorrect() {
		labelText.setBackground(new Color(null, new RGB(0, 128, 0)));
		labelText.setText("Correct");
	}
	
	private void displayError(int line) {
		labelText.setBackground(new Color(null, new RGB(255, 128, 0)));
		labelText.setText("Error detected: " + line);
	}

	public void addListener(IDocument document) {
		BytecodeListener listener = new BytecodeListener();
		document.addDocumentListener(listener);
	}

	/**
	 * @param editor
	 */
	public void setActiveEditor(IEditorPart editor) {
		activeEditor = editor;
	}
	
	public void reinit() {
		ready = false;
	}
	
	public boolean[] getModified() {
		return bcc.getModified();
	}
	
	public void setModTable(boolean[] modified) {
		this.modified = modified;
		modTable = true;
	}

	public String[] getCommentTab() {
		return bcc.getComments();
	}
}
