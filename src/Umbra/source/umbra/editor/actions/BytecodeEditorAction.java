/**
 * 
 */
package umbra.editor.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;

import umbra.editor.BytecodeEditorContributor;
import umbra.editor.Composition;
import umbra.editor.IColorValues;

/**
 *	This class defines an action of changing coloring style. It is used
 *  in two instances: one changes colors clockwise and the other 
 *  counter-clockwise.
 *  
 *  @author Wojtek W±s  
 */
public class BytecodeEditorAction extends Action {
	/**
	 * TODO
	 */
	private Shell shell;
	/**
	 * TODO
	 */
	private IEditorPart activeEditor;
	/**
	 * TODO
	 */
	private int change;
	
	/**
	 * TODO
	 */
	private int mod;
	
	/**
	 * TODO
	 */
	private BytecodeEditorContributor contributor;
	
	/**
	 * TODO
	 * @param contr TODO
	 * @param change	+1 for clockwise changing -1 otherwise.
	 */
	public BytecodeEditorAction(BytecodeEditorContributor contr, int change, 
			                    int mod) {
		super("Change color");
		this.change = change;
		this.mod = mod;
		this.contributor=contr;
	}
	
	/**
	 * TODO
	 */
	public void setShell(Shell shell) {
		this.shell = shell;
	}
	
	/**
	 * This method changes global value related to the coloring style
	 * and refreshes the editor window. 
	 */
	public void run() {
		if (mod == IColorValues.models.length - 1) return;
		mod = (mod + change) % (IColorValues.models.length - 1);
		Composition.setMod(mod);
		if (activeEditor != null){
			try {
				contributor.refreshEditor(activeEditor);
			} catch (PartInitException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}
	
	/**
	 * TODO
	 */
	public void setActiveEditor(IEditorPart part) {
		activeEditor = part;
		System.out.println(part.getTitle());
	System.out.println(this.toString());
	}
}