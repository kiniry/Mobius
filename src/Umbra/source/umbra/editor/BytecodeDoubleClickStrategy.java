package umbra.editor;

import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.ITextViewer;



/**
 * This class is responsible for action that is performed after
 * a double click event in a bytecode editor window. This triggers a
 * synchronization action which relates the position clicked within the
 * bytecode editor to the source code in the corresponding Java file editor.
 * 
 * @author 	Wojciech Wąs
 * @see		BytecodeDocument
 */
public class BytecodeDoubleClickStrategy implements ITextDoubleClickStrategy {

	/**
	 * This method implements the reaction on the double click in
	 * a bytecode editor. It synchronizes the position clicked within the
     * bytecode editor to the source code in the corresponding Java file 
     * editor. Most the information about the selected area is not used.
     * Only the position of the cursor is taken into account.
	 * 
	 * @param part the selected area of the bytecode document
	 */
	public void doubleClicked(ITextViewer part) {
		int pos = part.getSelectedRange().x;

		if (pos < 0)
			return;

		BytecodeDocument bDoc = (BytecodeDocument)part.getDocument();
		bDoc.synchronizeBS(pos);
	}
}
