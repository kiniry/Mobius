package umbra.editor.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.texteditor.AbstractTextEditor;
import umbra.editor.BytecodeDocument;

/**
 * This class defines action of synchronization bytecode
 * position with appropriate point in source code.
 *
 * @author Wojtek W±s  
 * @see BytecodeDocument
 */
public class BytecodeSynchrAction extends Action {
	
	/**
	 * TODO
	 */
	private AbstractTextEditor editor;
	
	/**
	 * TODO
	 */
	public BytecodeSynchrAction() {
		super("Synchronize");
	}
	
	/**
	 * TODO
	 */
	public void setActiveEditor(IEditorPart targetEditor) {
		editor = (AbstractTextEditor)targetEditor;
	}

	/**
	 * TODO
	 */
	public void run() {
		ITextSelection selection = (ITextSelection)editor.getSelectionProvider().getSelection();
		int off = selection.getOffset();
		BytecodeDocument bDoc = (BytecodeDocument)editor.getDocumentProvider().getDocument(editor.getEditorInput());
		bDoc.synchronizeBS(off);
	}		
}
