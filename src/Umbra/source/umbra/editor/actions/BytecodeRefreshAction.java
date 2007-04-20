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
 * @author Wojtek W±s 
 */
public class BytecodeRefreshAction extends Action {
	/**
	 * TODO
	 */
	private IEditorPart editor;
	
	/**
	 * TODO should be the same as in BytecodeEditorContributor
	 */
	private BytecodeContribution bytecodeContribution;

	/**
	 * TODO should be the same as in BytecodeEditorContributor
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
	 * TODO
	 */
	public void setActiveEditor(IEditorPart targetEditor) {
		editor = targetEditor;
	}

	/**
	 * This method firstly saves the editor and then
	 * creates new input from the JavaClass structure in BCEL. 
	 * Finally replaces content of the Editor window with
	 * the newly generated input.
	 */
	public void run() {
		editor.doSave(null);
		IPath active = ((FileEditorInput)editor.getEditorInput()).getFile().getFullPath();
		IFile file = ((FileEditorInput)editor.getEditorInput()).getFile();
		try {
			String[] commentTab = bytecodeContribution.getCommentTab();
			String[] interlineTab = bytecodeContribution.getInterlineTab();
			for (int i = 0; i < interlineTab.length; i++) {
				System.out.println("" + i + ". " + interlineTab[i]);
			}
			((BytecodeEditor)editor).refreshBytecode(active, commentTab, interlineTab);
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
		}
		contributor.synchrEnable();
	}
}
