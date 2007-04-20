package umbra.editor.actions;

import java.io.IOException;

import org.apache.bcel.classfile.*;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeEditor;
import umbra.editor.BytecodeEditorContributor;
import umbra.editor.actions.BytecodeRebuildAction;

/**
 * This class defines action that allows linking changes
 * made to bytecode with these made to source Java code
 * in case they are made to different methods.
 * If modification happens in the same method, Bytecode
 * modification is privileged.
 * 
 * @author Wojtek W±s  
 */
public class BytecodeCombineAction extends Action {
	/**
	 * TODO
	 */
	private IEditorPart editor;
	/**
	 * TODO
	 */
	private BytecodeEditorContributor contributor;

	/**
	 * TODO should be the same as in contributor
	 */
	private BytecodeContribution bytecodeContribution;
	
	/**
	 * TODO
	 * @param contributor
	 * @param bytecodeContribution 
	 */
	public BytecodeCombineAction(BytecodeEditorContributor contributor, 
			                     BytecodeContribution bytecodeContribution) {
		super("Combine");
		this.contributor = contributor;
		this.bytecodeContribution = bytecodeContribution;
	}
	
	/**
	 * The action is similar to rebuild - it generates
	 * input from the original source in the same way.
	 * The difference is that after this all methods are
	 * checked for bytecode modifications and if one
	 * has been made, it is chosen and saved from JavaClass.
	 * 
	 * @see BytecodeRebuildAction
	 */
	public void run() {
		JavaClass oldJc = ((BytecodeEditor)editor).getJavaClass();
		//System.out.println("OLD JAVA CLASS:");
		//controlPrint(oldJc, 1);
		//controlPrint(oldJc, 2);
		IEditorPart related = ((BytecodeEditor)editor).getRelatedEditor();
		if (related.isSaveOnCloseNeeded()) { 
			MessageDialog.openWarning(editor.getSite().getShell(), "Bytecode", "You must save it before!");
			return;
		}	
		IFile file = ((FileEditorInput)editor.getEditorInput()).getFile();
		IPath path = file.getFullPath();
		String fnameFrom = path.toOSString().replaceFirst(
				                  UmbraHelper.BYTECODE_EXTENSION,
				                  UmbraHelper.CLASS_EXTENSION);
		String lastSegment = path.lastSegment().replaceFirst(
				                  UmbraHelper.BYTECODE_EXTENSION,
				                  UmbraHelper.CLASS_EXTENSION);
		String fnameTo = path.removeLastSegments(1).append("_" + lastSegment).toOSString();
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot(); 
		IFile fileFrom = root.getFile(new Path(fnameFrom));
		IPath pathTo = new Path(fnameTo);
		IFile fileTo = root.getFile(pathTo);
		try {
			fileTo.delete(true, null);
			fileFrom.copy(pathTo, true, null);
		} catch (CoreException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		String clname = path.removeFileExtension().lastSegment();
		String pathName = ((BytecodeEditor)editor).getPath(path).toOSString();
		//System.out.println("WARNING: " + pathName + " D:\\smieci\\eclipse" + path.removeLastSegments(1).toOSString());
		ClassPath cp = new ClassPath(pathName);
		SyntheticRepository strin = SyntheticRepository.getInstance(cp);
		try {
			JavaClass jc = strin.loadClass(clname);
			//System.out.println("SOURCE JAVA CLASS:");
			//controlPrint(jc, 1);
			//controlPrint(jc, 2);
			strin.removeClass(jc);			
			ClassGen oldCg = new ClassGen(oldJc);
			ClassGen cg = new ClassGen(jc);
			int oldMeths = oldCg.getMethods().length;
			int meths = cg.getMethods().length;
			boolean[] modified = bytecodeContribution.getModified();
			for (int i = 0; i < modified.length && i < oldMeths && i < meths; i++) {
				if (modified[i]) cg.setMethodAt(oldCg.getMethodAt(i), i);
				System.out.println("" + i + (modified[i] ? " yes" : " no"));
			}
			jc = cg.getJavaClass();
			//System.out.println("NEW JAVA CLASS:");
			//controlPrint(jc, 1);
			//controlPrint(jc, 2);
			String fullName = ((BytecodeEditor)editor).getPath(path).toOSString();
			jc.dump(fullName + "\\" + lastSegment);
			//System.out.println("WARNING: " + fullName + "\\" + lastSegment + " D:\\smieci\\eclipse" + fnameFrom);
			((BytecodeEditor)editor).refreshBytecode(path, null, null);
			IEditorInput input = new FileEditorInput(file);
			contributor.refreshEditor(editor, input);
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (CoreException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		contributor.synchrEnable();
	}
	
	/**
	 * TODO
	 */
	public void setActiveEditor(IEditorPart part) {
		editor = part;
	}
}
