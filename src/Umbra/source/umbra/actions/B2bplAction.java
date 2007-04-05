package umbra.actions;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import org.apache.bcel.classfile.JavaClass;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspace;
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

import umbra.editor.BytecodeEditor;
import b2bpl.Main;
import b2bpl.Project;

/**
 * This action is used to convert Java Bytecode into BoogiePL.
 * The following JAR packages are required:
 *   - b2bpl.jar
 *   - asm.jar
 * 
 * @author Samuel Willimann
 *
 */
public class B2bplAction implements IEditorActionDelegate {
	
	private final String MESSAGE_DIALOG_TITLE = "Bytecode To BoogiePL";
	private final String BYTECODE_EXTENSION = ".btc";
	private final String BOOGIEPL_EXTENSION = ".bpl";
	
	/**
	 * TODO
	 */
	private IEditorPart editor;

	/**
	 * TODO
	 */
	public void setActiveEditor(IAction action, IEditorPart targetEditor) {
		editor = targetEditor;
	}

	/**
	 * TODO
	 */
	public void run(IAction action) {

		IPath active = ((FileEditorInput)editor.getEditorInput()).getFile().getFullPath();
		if (editor.isSaveOnCloseNeeded()) {
			MessageDialog.openWarning(editor.getSite().getShell(), MESSAGE_DIALOG_TITLE, "You must save the bytecode before you translate it into BoogiePL.");
			return;
		}
		int lind = active.toOSString().lastIndexOf(BYTECODE_EXTENSION);
		if (lind == -1) MessageDialog.openInformation(editor.getSite().getShell(), MESSAGE_DIALOG_TITLE, "This is not a \"" + BYTECODE_EXTENSION + "\" file.");
		else {
			//replaceClass(active);

		
			//editor.doSave(null);
			//IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			//IProject project = root.getProject("selectedProject name");
			//String entirePath = p.getLocation().toOSString(); 
			
			IFile file = ((FileEditorInput)editor.getEditorInput()).getFile();
			
			//String location = root.getLocation().toString();
	
			String projectPath = file.getProject().getLocation().toOSString();
			String bytecodePath = file.getLocation().toOSString();
			String boogiePLPath = bytecodePath.replace(BYTECODE_EXTENSION, BOOGIEPL_EXTENSION);
			String javaPath     = bytecodePath.replace(BYTECODE_EXTENSION, "" /*.class" */).substring(projectPath.length() + 1 ).replace('\\', '.');
			
			List<String> args = new ArrayList<String>();	
			args.add("-basedir"); args.add(projectPath);
			args.add("-o"); args.add(boogiePLPath);
			args.add(javaPath);
			
			String[] argsArray = args.toArray(new String[args.size()]);
			
			// MessageDialog.openError(editor.getSite().getShell(), "Bytecode", "B");
			
			try {
				PrintWriter messageWriter = new PrintWriter(boogiePLPath);
				Project p = Project.fromCommandLine(argsArray, messageWriter);
				Main main = new Main(p);
				main.compile();
			} catch (IOException ioex) {
				System.out.println(ioex.toString());
			}
			
			//-------------- Load .bpl file in editor
			
			String actlind = active.toOSString().substring(0, lind);
			String fname = actlind + BOOGIEPL_EXTENSION;
			IWorkspace workspace = ResourcesPlugin.getWorkspace();
			file = workspace.getRoot().getFile(new Path(fname));
			FileEditorInput input = new FileEditorInput(file);
			try {
				IWorkbenchPage page = editor.getEditorSite().getPage();
				BytecodeEditor bplEditor = (BytecodeEditor)page.openEditor(input, "umbra.BoogiePLEditor", true);
				bplEditor.refreshBytecode(active, null, null);
				input = new FileEditorInput(file);
				JavaClass jc = bplEditor.getJavaClass();
				page.closeEditor(bplEditor, true);
				bplEditor = (BytecodeEditor)page.openEditor(input, "umbra.BoogiePLEditor", true);
				bplEditor.setRelation((AbstractDecoratedTextEditor)editor, jc);
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
	 * TODO
	 */
	public void selectionChanged(IAction action, ISelection selection) {
		// TODO Auto-generated method stub

	}

}