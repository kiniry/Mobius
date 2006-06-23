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
 * @author Wojtek W�s
 */
public class BytecodeContribution extends ControlContribution { 
	
	/**
     * TODO write description
     */
    private int num = 0;
	/**
     * TODO write description
     */
    private boolean needNew = true;
    /**
     * TODO write description
     */    
	private IEditorPart activeEditor;
    /**
     * TODO write description
     */    
	private Label labelNum;
    /**
     * TODO write description
     */    
    private Label labelOff;
    /**
     * TODO write description
     */    
    private Label labelText;
    /**
     * TODO write description
     */    
	private static BytecodeContribution inUse;
    /**
     * TODO write description
     */    
	private BytecodeController bcc;	
    /**
     * TODO write description
     */    
	private boolean ready = false;
    /**
     * TODO write description
     */    
	private boolean modTable = false;
    /**
     * TODO write description
     */    
	private boolean[] modified;
	
    /**
     * TODO write description
     * 
     * @param doc TODO write description
     * @throws TODO write description
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
		return;
	}
	
    /**
     * TODO write description
     */    
	public class BytecodeListener implements IDocumentListener {
		
        /**
         * TODO write description
         */    
		int startRem = -1;
        /**
         * TODO write description
         */    
        int stopRem = -1;
		
        /**
         * TODO write description
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
			bcc.checkAllLines(start, stop);
			if (!bcc.allCorrect()) 
				displayError(bcc.getFirstError());
			else displayCorrect();
		}
		
	}
	
    /**
     * TODO write description
     */    
	protected BytecodeContribution() {
		super("Bytecode");
		inUse = this;
	}
	
    /**
     * TODO write description
     * 
     * @return TODO write description
     */    
	public static BytecodeContribution inUse() {
		return inUse;
	}
	
    /**
     * TODO write description
     * 
     * @return TODO write description
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
     * TODO write description
     */    
	public void survive() {
		needNew = false;
	}
	
    /**
     * TODO write description
     * 
     * @param parent TODO write description
     * @return TODO write description
     */    
	protected Control createControl(Composite parent) {
		Composite composite = new Composite(parent, SWT.BORDER);
		composite.setData(this);

		labelText = new Label(composite, SWT.NONE);
		labelText.setSize(120, 15);
		labelText.setFont(new Font(null, "Arial", 8, 1));
		labelText.setForeground(new Color(null, new RGB(255, 255, 0)));
		return composite;
	}
	
    /**
     * TODO write description
     */    
	private void displayCorrect() {
		labelText.setBackground(new Color(null, new RGB(0, 128, 0)));
		labelText.setText("Correct");
	}
	
    /**
     * TODO write description
     * 
     * @param line TODO write description
     */    
	private void displayError(int line) {
		labelText.setBackground(new Color(null, new RGB(255, 128, 0)));
		labelText.setText("Error detected: " + line);
	}

    /**
     * TODO write description
     * 
     * @param document TODO write description
     */    
	public void addListener(IDocument document) {
		BytecodeListener listener = new BytecodeListener();
		document.addDocumentListener(listener);
	}

	/**
     * TODO write description
     * 
	 * @param editor TODO write description
	 */
	public void setActiveEditor(IEditorPart editor) {
		activeEditor = editor;
	}
	
    /**
     * TODO write description
     */    
	public void reinit() {
		ready = false;
	}
	
    /**
     * TODO write description
     * 
     * @return TODO write description
     */    
	public boolean[] getModified() {
		return bcc.getModified();
	}
	
    /**
     * TODO write description
     * 
     * @param TODO write description
     */    
	public void setModTable(boolean[] modified) {
		this.modified = modified;
		modTable = true;
	}

    /**
     * TODO write description
     * 
     * @return TODO write description
     */    
	public String[] getCommentTab() {
		return bcc.getComments();
	}
	
	/**
     * TODO write description
     * 
     * @return TODO write description
     */
     public String[] getInterlineTab() {
		return bcc.getInterline();
	}
}
