/**
 * 
 */
package umbra.editor.actions;

import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.action.Action;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeEditor;
import umbra.editor.BytecodeEditorContributor;


/**
 * This is a class defining an action: save current bytecode 
 * editor window and re-generate Bytecode from BCEL structures.
 * This action is equal to generating bytecode again from the
 * Java code after saving binary file.
 * 
 * @author Wojtek Wąs 
 */
public class BytecodeRefreshAction extends Action {

	/**
	 * The current bytecode editor for which the action takes place.
	 */
	private IEditorPart editor;
	
	/**
	 * TODO should be the same as in BytecodeEditorContributor
	 */
	private BytecodeContribution bytecodeContribution;

	/**
	 * The manager that initialises all the actions within the
	 * bytecode plugin.
	 */
	private BytecodeEditorContributor contributor;
	
	/**
	 * TODO
	 * @param contributor 
	 * @param bytecodeContribution 
	 */
	public BytecodeRefreshAction(BytecodeEditorContributor contrib, 
			                     BytecodeContribution bytecodeContrib) {
		super("Refresh");
		bytecodeContribution = bytecodeContrib;
		contributor = contrib;
	}

	/**
	 * This method sets the bytecode editor for which the
	 * refresh action will be executed.
	 * 
	 * @param targetEditor the bytecode editor for which the action will be 
	 *                     executed
	 */
	public void setActiveEditor(IEditorPart targetEditor) {
		editor = targetEditor;
		if (!editor.isDirty()) setEnabled(false);
	}

	/**
	 * This method firstly saves the editor and then
	 * creates new input from the JavaClass structure in BCEL. 
	 * Finally replaces content of the Editor window with
	 * the newly generated input.
	 * 
	 * TO powinno dzia�a� tak, �e po zmianie, reformatowane
	 * jest wszystko zgodnie ze standardem 
	 * 
	 * po przejsciu do javy refresh sie robi disabled
	 */
	public void run() {
		editor.doSave(null);
		try {
		IFile file = ((FileEditorInput)editor.getEditorInput()).getFile();
		IPath active = file.getFullPath();
		try {
			String[] commentTab = bytecodeContribution.getCommentTab();
			String[] interlineTab = bytecodeContribution.getInterlineTab();
			System.err.println(interlineTab.length);
			for (int i = 0; i < interlineTab.length; i++) {
				System.out.println("" + i + ". " + interlineTab[i]);
				System.err.println("" + i + ". " + interlineTab[i]);
			}
			((BytecodeEditor)editor).refreshBytecode(active, commentTab, 
					                                 interlineTab);
			FileEditorInput input = new FileEditorInput(file);
			boolean[] modified = bytecodeContribution.getModified();
			bytecodeContribution.setModTable(modified);
			contributor.refreshEditor(editor, input);
		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		} catch (CoreException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		} } catch (RuntimeException re) {
			re.printStackTrace();
			throw re;
		}
		contributor.synchrEnable();
	}
}
