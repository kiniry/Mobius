/*
 * Created on 2005-09-06
 */
package umbra;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

/**
 * This class defines an action that adds current bytecode
 * to history.
 * 
 * @author Wojtek W¹s
 */
public class HistoryAction implements IEditorActionDelegate {

	private IEditorPart editor;
	
	public void setActiveEditor(IAction action, IEditorPart targetEditor) {
		editor = targetEditor;
	}

	public void run(IAction action) { 
		int num = ((BytecodeEditor)editor).newHistory();
		if (num == -1) {
			MessageDialog.openInformation(editor.getEditorSite().getShell(), "History", "History is already full.");
			return;
		}
		String ext = ".bt" + num;
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		IFile fileFrom = ((FileEditorInput)editor.getEditorInput()).getFile();
		IPath active = fileFrom.getFullPath();
		String fnameTo = active.toOSString().replaceFirst(".btc", ext);
		IPath pathTo = new Path(fnameTo);
		IFile fileTo = root.getFile(pathTo);
		try {
			fileTo.delete(true, null);
			fileFrom.copy(pathTo, true, null);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		String lastSegment = active.lastSegment().replaceFirst(".btc", ".class");
		String clnameFrom = active.removeLastSegments(1).append(lastSegment).toOSString();
		String clnameTo = active.removeLastSegments(1).append("_" + num + "_" + lastSegment).toOSString();
		IFile classFrom = root.getFile(new Path(clnameFrom));
		IPath clpathTo = new Path(clnameTo);
		IFile classTo = root.getFile(clpathTo);
		try {
			classTo.delete(true, null);
			classFrom.copy(clpathTo, true, null);
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	public void selectionChanged(IAction action, ISelection selection) {
	
	}

}
