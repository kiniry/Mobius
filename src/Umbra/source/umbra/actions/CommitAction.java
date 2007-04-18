package umbra.actions;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;

/**
 * The action is used to commit changes made to Java source code.
 * After running it the rebuild action will create a Bytecode related
 * to the commited version.
 * 
 * @author Wojciech W±s
 *
 */
public class CommitAction implements IEditorActionDelegate {
	
	/**
	 * The editor for the corresponding Java file.
	 */
	private IEditorPart editor;

	/**
	 * The method saves the editor for the Java code file.
	 */
	public void setActiveEditor(IAction action, IEditorPart targetEditor) {
		editor = targetEditor;
	}

	/**
	 * This method is invoked when the Umbra "Commit" button is pressed
	 * in a Java file editor. It saves the current Java file and deletes
	 * from workspace the original class file which contains the result
	 * of Java compilation (@see BytecodeEditor#doSave(IProgressMonitor)).
	 * 
	 * @param action the action that triggered the operation 
	 * @see IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
			editor.doSave(null);
			IFile file = ((FileEditorInput)editor.getEditorInput()).getFile();
			IPath active = file.getFullPath();
			String lastSegment = UmbraHelper.replaceLast(active.lastSegment(), 
					                               UmbraHelper.JAVA_EXTENSION, 
					                               UmbraHelper.CLASS_EXTENSION);
			String fnameFrom = active.removeLastSegments(1).
			                          append("_" + lastSegment).toOSString();
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot(); 
			IFile fileFrom = root.getFile(new Path(fnameFrom));
			try {
				fileFrom.delete(true, null);
			} catch (CoreException e) {
				e.printStackTrace();
			}
	}

	/**
	 * The method reacts when the selected area changes in the Java
	 * source code editor. Currently, it does nothing.
	 */
	public void selectionChanged(IAction action, ISelection selection) {
	}

}
