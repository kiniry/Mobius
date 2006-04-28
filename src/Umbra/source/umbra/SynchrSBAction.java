/*
 * Created on 2005-07-20
 */
package umbra;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.AbstractTextEditor;

/**
 * This class defines an action of synchronization positions
 * form source code to bytecode. It is available with the standard
 * Java editor.
 * 
 * @author Wojtek W¹s
 * @see DocumentProvider
 */
public class SynchrSBAction implements IEditorActionDelegate {
	private AbstractTextEditor editor;
	
	public void setActiveEditor(IAction action, IEditorPart targetEditor) {
		editor = (AbstractTextEditor)targetEditor;
	}

	public void run(IAction action) {
		ITextSelection selection = (ITextSelection)editor.getSelectionProvider().getSelection();
		int off = selection.getOffset();
		IPath active = ((FileEditorInput)editor.getEditorInput()).getFile().getFullPath();	
		int lind = active.toOSString().lastIndexOf(".java");
		if (lind == -1) {
			MessageDialog.openError(editor.getSite().getShell(), "Bytecode", "This is not a \".java\" file");
			return;
		}
		String actlind = active.toOSString().substring(0, lind);
		String fname = actlind + ".btc";
		IWorkspace workspace = ResourcesPlugin.getWorkspace();
		IFile file = workspace.getRoot().getFile(new Path(fname));
		if (!file.exists()) {
			MessageDialog.openError(editor.getSite().getShell(), "Bytecode", "File " + fname + " not found");
			return;
		} 
		FileEditorInput input = new FileEditorInput(file);
		try {
			BytecodeEditor bcEditor = (BytecodeEditor)editor.getSite().getPage().openEditor(input, "umbra.BytecodeEditor", true);
			if (bcEditor.isSaveOnCloseNeeded()) {
				MessageDialog.openWarning(editor.getSite().getShell(), "Bytecode", "The Bytecode editor needs being refreshed!");
				return;
			}
			BytecodeDocument bDoc = ((BytecodeDocument)bcEditor.getDocumentProvider().getDocument(input));
			bDoc.synchronizeSB(off, bcEditor);
		} catch (PartInitException e) {
			e.printStackTrace();
		}
	}

	public void selectionChanged(IAction action, ISelection selection) {

	}

}
