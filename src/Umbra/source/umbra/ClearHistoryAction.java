/*
 * Created on 2005-09-06
 *
 */
package umbra;

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

/**
 * The action that removes historical versions of code.
 * 
 * @author Wojtek W�s
 */
public class ClearHistoryAction implements IEditorActionDelegate {

    /**
     * TODO write description
     */
    private IEditorPart editor;
	
    /**
     * TODO write description
     * 
     * @param action TODO write description
     * @param targetEditor TODO write description
     */
    public void setActiveEditor(IAction action, IEditorPart targetEditor) {
		editor = targetEditor;
	}

    /**
     * TODO write description
     * 
     * @param action TODO write description
     */
    public void run(IAction action) {
		((BytecodeEditor)editor).clearHistory();
		for (int i = 0; i <= IHistory.maxHistory; i++) {
			String ext = ".bt" + i; 
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			IFile inputFile = ((FileEditorInput)editor.getEditorInput()).getFile();
			IPath active = inputFile.getFullPath();
			String fname = active.toOSString().replaceFirst(".btc", ext); 
			IFile file = root.getFile(new Path(fname));
			try {
				file.delete(true, null);
			} catch (CoreException e) {
				e.printStackTrace();
			}
			String lastSegment = active.lastSegment().replaceFirst(".btc", ".class");
			String clname = active.removeLastSegments(1).append("_" + i + "_" + lastSegment).toOSString(); 
			IFile classFile = root.getFile(new Path(clname));
			try {
				classFile.delete(true, null);
			} catch (CoreException e) {
				e.printStackTrace();
			}
		}
	
	}

    /**
     * TODO write description
     * 
     * @param action TODO write description
     * @param selection TODO write description
     */
    public void selectionChanged(IAction action, ISelection selection) {

	}

}
