/*
 * Created on 2005-07-20
 */
package umbra.java.actions;

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

import umbra.UmbraHelper;
import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeEditor;

/**
 * This class defines an action of synchronization positions
 * form source code to bytecode. It is available with the standard
 * Java editor.
 * 
 * @author Wojtek Wąs
 * @see DocumentProvider
 */
public class SynchrSBAction implements IEditorActionDelegate {
	
	/**
	 * The editor of the Java source code.
	 */
	private AbstractTextEditor editor;
	
	/**
	 * The method sets the internal editor attribute.
	 */
	public void setActiveEditor(IAction action, IEditorPart targetEditor) {
		editor = (AbstractTextEditor)targetEditor;
	}

	/**
	 * This method handles the action of the syncronisation between the
	 * source code and the bytecode i.e. it takes the selection in
	 * the source code and shows the corresponding selection in the
	 * bytecode.  
	 * 
	 * @param action the action that triggered the operation
	 */
	public void run(IAction action) {
		ITextSelection selection = (ITextSelection)editor.
		                                getSelectionProvider().getSelection();
		int off = selection.getOffset();
		IPath active = ((FileEditorInput)editor.getEditorInput()).
		                                        getFile().getFullPath();	
		int lind = active.toOSString().lastIndexOf(UmbraHelper.JAVA_EXTENSION);
		if (lind == -1) {
			MessageDialog.openError(editor.getSite().getShell(), 
					                "Bytecode", 
					                "This is not a \""+
					                UmbraHelper.JAVA_EXTENSION+
					                "\" file");
			return;
		}
		String fname = UmbraHelper.replaceLast(active.toOSString(),
									UmbraHelper.JAVA_EXTENSION,
									UmbraHelper.BYTECODE_EXTENSION);
		IWorkspace workspace = ResourcesPlugin.getWorkspace();
		IFile file = workspace.getRoot().getFile(new Path(fname));
		if (!file.exists()) {
			MessageDialog.openError(editor.getSite().getShell(), 
					                "Bytecode", 
					                "File " + fname + " not found");
			return;
		} 
		FileEditorInput input = new FileEditorInput(file);
		try {
			BytecodeEditor bcEditor = (BytecodeEditor)editor.getSite().
			                                       getPage().
			                                       openEditor(input, 
			                                    		"umbra.BytecodeEditor", 
			                                    		true);
			if (bcEditor.isSaveOnCloseNeeded()) {
				MessageDialog.openWarning(editor.getSite().getShell(), 
						                  "Bytecode", 
						                  "The Bytecode editor needs being "+
						                  "refreshed!");
				return;
			}
			BytecodeDocument bDoc = ((BytecodeDocument)bcEditor.
					                            getDocumentProvider().
					                            getDocument(input));
			bDoc.synchronizeSB(off, bcEditor);
		} catch (PartInitException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Currently, does nothing.
	 */
	public void selectionChanged(IAction action, ISelection selection) {
	}

}
