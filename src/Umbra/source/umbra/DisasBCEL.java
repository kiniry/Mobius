/*
 * Created on 2005-04-21
 *
 */
package umbra;

import java.io.IOException;

import org.apache.bcel.classfile.JavaClass;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspace;
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
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditor;

/**
 * This class defines the action related to Java source editor.
 * Its execution causes generating new related bytecode file
 * in new editor window.
 * 
 * @author BYTECODE team
 */

public class DisasBCEL implements IEditorActionDelegate {
	
	private IEditorPart editor;

	/**
	 * Finds JavaClass structure related to the current Java
	 * source. Generates new bytecode from it and displays
	 * it in a new bytecode editor window.
	 */
	
	public void run(IAction action) {
		IPath active = ((FileEditorInput)editor.getEditorInput()).getFile().getFullPath();
		if (editor.isSaveOnCloseNeeded()) {
			MessageDialog.openWarning(editor.getSite().getShell(), "Bytecode", "You must save it before!");
			return;
		}	
		int lind = active.toOSString().lastIndexOf(".java");
		if (lind == -1) MessageDialog.openInformation(editor.getSite().getShell(), "Bytecode", "This is not a \".java\" file");
		else {
			//replaceClass(active);
			String actlind = active.toOSString().substring(0, lind);
			String fname = actlind + ".btc";
			IWorkspace workspace = ResourcesPlugin.getWorkspace();
			IFile file = workspace.getRoot().getFile(new Path(fname));
			FileEditorInput input = new FileEditorInput(file);
			try {
				IWorkbenchPage page = editor.getEditorSite().getPage();
				BytecodeEditor bcEditor = (BytecodeEditor)page.openEditor(input, "umbra.BytecodeEditor", true);
				bcEditor.refreshBytecode(active, null, null);
				input = new FileEditorInput(file);
				JavaClass jc = bcEditor.getJavaClass();
				Composition.startDisas();
				page.closeEditor(bcEditor, true);
				bcEditor = (BytecodeEditor)page.openEditor(input, "umbra.BytecodeEditor", true);
				bcEditor.setRelation((AbstractDecoratedTextEditor)editor, jc);
				Composition.stopDisas();
			} catch (CoreException e) {
				e.printStackTrace();
			} catch (ClassNotFoundException e) {
				e.printStackTrace();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
	
	private void replaceClass(IPath active) {
		String fnameFrom = active.toOSString().replaceFirst(".java", ".class");
		String lastSegment = active.lastSegment().replaceFirst(".java", ".class");
		String fnameTo = active.removeLastSegments(1).append("_" + lastSegment).toOSString();
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot(); 
		IFile fileFrom = root.getFile(new Path(fnameFrom));
		IPath pathTo = new Path(fnameTo);
		IFile fileTo = root.getFile(pathTo);
		try {
			fileTo.delete(true, null);
			fileFrom.copy(pathTo, true, null);
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}
	

	public void selectionChanged(IAction action, ISelection selection) {
	}

	public void setActiveEditor(IAction action, IEditorPart targetEditor) {
		editor = targetEditor;
	}

}
