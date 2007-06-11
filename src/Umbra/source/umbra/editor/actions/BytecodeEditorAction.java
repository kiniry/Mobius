/**
 * 
 */
package umbra.editor.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;

import umbra.editor.BytecodeEditorContributor;
import umbra.editor.Composition;
import umbra.editor.IColorValues;

/**
 *	This class defines an action of changing coloring style. Two 
 *  instances of the class are used - one increases the coloring
 *  style mode and the other decreased the mode.
 *  
 *  @author Wojtek Wąs  
 */
public class BytecodeEditorAction extends Action {
	/**
	 * The current bytecode editor for which the action takes place.
	 */
	private IEditorPart activeEditor;
	
	/**
	 * The number which decides on how the colouring mode
	 * changes (+1 for increasing, -1 for decreasing);
	 */
	private int change;
	//@ invariant change==1 || change == -1;
	
	/**
	 * The current colouring style, see {@link IColorValues}
	 */
	private int mod;
	
	/**
	 * The manager that initialises all the actions within the
	 * bytecode plugin.
	 */
	private BytecodeEditorContributor contributor;
	
	/**
	 * This constructor creates the action to change the
	 * clouring mode. 
	 * 
	 * @param contr TODO
	 * @param change +1 for increasing, -1 for decreasing the colouring
	 *        mode
	 * @param the initial colouring mode
	 */
	/*@ requires change==1 || change == -1;
	  @
	  @*/
	public BytecodeEditorAction(BytecodeEditorContributor contr, 
			                    int change, 
			                    int mod) {
		super("Change color");
		this.change = change;
		this.mod = mod;
		this.contributor=contr;
	}
	
	
	/**
	 * This method changes global value related to the coloring style
	 * and refreshes the editor window. 
	 */
	public void run() {
		if (mod == IColorValues.MODELS.length - 1) return;
		mod = (mod + change) % (IColorValues.MODELS.length - 1);
		Composition.setMod(mod);
		if (activeEditor != null){
			try {
				contributor.refreshEditor(activeEditor);
			} catch (PartInitException e) {
				MessageDialog.openWarning(activeEditor.getSite().getShell(), 
						"Bytecode", "Cannot open a new editor after closing "+
						            "the old one");
			}
		}
	}
	
	/**
	 * This method sets the bytecode editor for which the
	 * action to change the colouring mode will be executed.
	 * 
	 * @param part the bytecode editor for which the action will be 
	 *        executed
	 */
	public void setActiveEditor(IEditorPart part) {
		activeEditor = part;
		mod = Composition.getMod();
	}
}