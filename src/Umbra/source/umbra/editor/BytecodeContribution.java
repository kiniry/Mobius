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
 * @author Wojtek Wąs
 */
public class BytecodeContribution extends ControlContribution { 
	
	/**
	 * TODO
	 */
	private boolean needNew = true;
	
	/**
	 * Text of the status label: "Correct", "Error in line ..." etc.
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
	 * This array keeps track of which methods in the class edited by the
	 * bytecode editor are modified. It contains <code>true</code> on i-th
	 * position when the i-th method is modified. 
	 * 
	 * TODO it's not completely true, the modified in bcc is the actual
	 * point
	 */
	private boolean[] modified;
	
	/**
	 * The manager that initialises all the actions within the
	 * bytecode plugin.
	 */
	private BytecodeEditorContributor editorContributor;

	
	/**
	 * This method initialises the internal structures of the bytecode
	 * contribution. In particular it initialises the object that
	 * manages the BCEL operations and enables the relevant actions
	 * in the Umbra plugin bytecode contributor.
	 * 
	 * TODO what's modTable
	 */
	private void init(IDocument doc) {
		bcc = new BytecodeController();
		bcc.init(doc);
		if (modTable) {
			bcc.setModified(modified);
			modTable = false;
		}
		bcc.checkAllLines(0, doc.getNumberOfLines() - 2);
		ready = true;
		editorContributor.getRefreshAction().setEnabled(true);
	}
	
	/**
	 * This is a listener class that receives all the events that
	 * change the content of the current bytecode document.
	 */
	public class BytecodeListener implements IDocumentListener {
				
		/**
		 * The current constructor does nothing.
		 */
		public BytecodeListener() {
		}

		/**
		 * Data passed from documentAboutToBeChanged to documentChanged.
		 * Should be null if no event is currently being processed.
		 */
		private DocumentEvent current_event = null;
		private int endLine;
		
		/**
		 * This method handles the event of the change in the current 
		 * bytecode document. This method is called before the textual
		 * change is made. This method initialises the BytecodeContribution
		 * object in case it has not been initialised yet. 
		 * 
		 * @param event the event that triggers the change, it should be
		 * the same as in {@ref #documentChanged(DocumentEvent)}
		 * 
		 * @see org.eclipse.jface.text.IDocumentListener#documentAboutToBeChanged(org.eclipse.jface.text.DocumentEvent)
		 */
		public void documentAboutToBeChanged(DocumentEvent event) {
			if (!ready) 
				init(event.fDocument); //this marks ready as true
			System.out.println("documentAboutToBeChanged "+event.getText());
			System.out.println("documentAboutToBeChanged "+event.getModificationStamp());
			System.out.println("documentAboutToBeChanged "+event.getOffset());
			System.out.println("documentAboutToBeChanged "+event.getLength());
			System.out.println("documentAboutToBeChanged "+event.getDocument().hashCode());
			System.out.flush();
			current_event = event;
			
			try {
				endLine = event.fDocument.getLineOfOffset(
							event.getOffset() + event.getLength());
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
		 * @param event the event that triggers the change, it should be
		 * the same as in {@ref #documentAboutToBeChanged(DocumentEvent)}
		 * 
		 * @see org.eclipse.jface.text.IDocumentListener#documentChanged(org.eclipse.jface.text.DocumentEvent)
		 */
		public void documentChanged(DocumentEvent event) {
			System.out.println("documentChanged "+event.getText());
			System.out.flush();
			int stop = 0;
			int startRem =0, stopRem = 0;
			try {
				startRem = event.fDocument.getLineOfOffset(event.getOffset());
				int insertedLen = event.getText().length();
				stop = event.fDocument.getLineOfOffset(event.getOffset() + 
						insertedLen);
				if (event == current_event) {
					stopRem = endLine;
				} else {
					throw new RuntimeException("documentChanged event does not match documentAboutToBeChanged event");
				}
				current_event = null;
			} catch (BadLocationException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			bcc.removeIncorrects(startRem, stopRem);
			bcc.addAllLines(event.fDocument, startRem, stopRem, stop);
			bcc.checkAllLines(startRem, stop);
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
		labelText.setText("Error detected: " + line);
	}

	/**
	 * TODO
	 */
	public void addListener(IDocument document) {
		System.out.println("addListener");
		BytecodeDocument doc = (BytecodeDocument) document;
		if (doc.isListenerAdded()) {
			BytecodeListener listener = new BytecodeListener();
			document.addDocumentListener(listener);
		}
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
