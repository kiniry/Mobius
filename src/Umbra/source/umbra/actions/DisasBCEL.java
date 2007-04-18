/*
 * Created on 2005-04-21
 *
 */
package umbra.actions;

import java.io.IOException;

import org.apache.bcel.classfile.JavaClass;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspace;
//import org.eclipse.core.resources.IWorkspaceRoot;
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

import umbra.UmbraHelper;
import umbra.editor.BytecodeEditor;
import umbra.editor.Composition;

/**
 * This class defines the action related to Java source editor.
 * Its execution causes generating new related bytecode file
 * in a new editor window.
 * 
 * @author BYTECODE team
 */

public class DisasBCEL implements IEditorActionDelegate {
	
	/**
	 * The title of the window with messages generated from within the
	 * objects of the DisasBCEL.
	 */
	private final String MESSAGE_DIALOG_TITLE = "Disassemble Bytecode";
	
	/**
	 * The editor of a Java file for which the bytecode file is
	 * generated.
	 */
	private IEditorPart editor;

	/**
	 * Finds JavaClass structure related to the current Java
	 * source. Generates new bytecode from it and displays
	 * it in a new bytecode editor window.
	 * 
	 * @param see the IActionDelegate.run(IAction)
	 */
	public void run(IAction action) {
		IPath active = ((FileEditorInput)editor.getEditorInput()).
			getFile().getFullPath();
		if (editor.isSaveOnCloseNeeded()) {
			MessageDialog.openWarning(editor.getSite().getShell(), 
									  MESSAGE_DIALOG_TITLE, 
									  "You must save the code before you "+
									  "disassemble it.");
			return;
		}
		int lind = active.toOSString().lastIndexOf(UmbraHelper.JAVA_EXTENSION);
		if (lind == -1) MessageDialog.openInformation(editor.getSite().
				                                             getShell(), 
				                                  MESSAGE_DIALOG_TITLE, 
				                                  "This is not a \"" + 
				                                  UmbraHelper.JAVA_EXTENSION + 
				                                  "\" file.");
		else {
			//replaceClass(active);
			String fname = UmbraHelper.replaceLast(active.toOSString(), 
					                            UmbraHelper.JAVA_EXTENSION,
					                            UmbraHelper.BYTECODE_EXTENSION); 
			IWorkspace workspace = ResourcesPlugin.getWorkspace();
			IFile file = workspace.getRoot().getFile(new Path(fname));
			FileEditorInput input = new FileEditorInput(file);
			try {
				IWorkbenchPage page = editor.getEditorSite().getPage();
				//BytecodeEditor bcEditor = (BytecodeEditor)page.openEditor(input, "org.eclipse.jdt.ui.CompilationUnitEditor", true);
				BytecodeEditor bcEditor = (BytecodeEditor)page.openEditor(input,
						"umbra.BytecodeEditor", 
						true);
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
	
	/**
	 * T ODO
	 * /
	private void replaceClass(IPath active) {
		String fnameFrom = active.toOSString().replaceFirst(JAVA_EXTENSION, 
				                                            CLASS_EXTENSION);
		String lastSegment = active.lastSegment().replaceFirst(JAVA_EXTENSION, 
				                                               CLASS_EXTENSION);
		String fnameTo = active.removeLastSegments(1).
		                        append("_" + lastSegment).toOSString();
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
	*/

	/**
	 * Currently, does nothing.
	 */
	public void selectionChanged(IAction action, ISelection selection) {
	}

	/**
	 * It sets the editor with the Java source code.
	 */
	public void setActiveEditor(IAction action, IEditorPart targetEditor) {
		editor = targetEditor;
	}

}
