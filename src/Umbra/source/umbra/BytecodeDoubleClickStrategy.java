package umbra;

import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.ITextViewer;

/**
 * This class is responsible for action that is executed after
 * double clicking in Bytecode editor window. Synchronization
 * to Java code window is then made.
 * 
 * @author 	Wojciech W¹s
 * @see		BytecodeDocument
 */

public class BytecodeDoubleClickStrategy implements ITextDoubleClickStrategy {

	public void doubleClicked(ITextViewer part) {
		int pos = part.getSelectedRange().x;

		if (pos < 0)
			return;

		BytecodeDocument bDoc = (BytecodeDocument)part.getDocument();
		bDoc.synchronizeBS(pos);
	}
	

}
