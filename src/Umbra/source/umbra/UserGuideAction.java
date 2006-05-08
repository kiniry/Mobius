/*
 * Created on 2005-09-06
 */
package umbra;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

/**
 * @author Wojtek W¹s
 */
public class UserGuideAction implements IEditorActionDelegate {

	private IEditorPart editor;
	
	public void setActiveEditor(IAction action, IEditorPart targetEditor) {
		editor = targetEditor;
	}

	public void run(IAction action) {

		IWorkspace workspace = ResourcesPlugin.getWorkspace();
		IFile file = workspace.getRoot().getFile(new Path("\\Info\\guide.txt"));
		FileEditorInput input = new FileEditorInput(file); 
		try {
			editor.getEditorSite().getPage().openEditor(input, "org.eclipse.ui.DefaultTextEditor");
		} catch (PartInitException e) {
			e.printStackTrace();
		}
	}


	public void selectionChanged(IAction action, ISelection selection) {

	}

}
