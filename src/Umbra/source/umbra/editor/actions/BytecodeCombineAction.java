package umbra.editor.actions;

import java.io.IOException;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeEditor;
import umbra.editor.BytecodeEditorContributor;

/**
 * This is an action associated with a bytecode editor (an 
 * extension .btc). The action allows linking changes
 * made to bytecode with the ones made to the source Java code.
 * The current implementation works only when the changes are
 * made to different methods. In case a modification happens in the 
 * same method, the bytecode modification is privileged.
 * 
 * @author Wojtek Wąs  
 */
public class BytecodeCombineAction extends Action {

	/**
	 * The current bytecode editor for which the action takes place.
	 */
	private IEditorPart editor;
	
	/**
	 * The manager that initialises all the actions within the
	 * bytecode plugin.
	 */
	private BytecodeEditorContributor contributor;

	/**
	 * TODO should be the same as in contributor 
	 */
	private BytecodeContribution bytecodeContribution;
	//@ invariant contributor.bytecodeContribution==bytecodeContribution;
	
	/**
	 * TODO
	 * 
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
	 * TODO
	 * 
	 * @see BytecodeRebuildAction
	 */
	public void run() {
		IEditorPart related = ((BytecodeEditor)editor).getRelatedEditor();
		if (related.isSaveOnCloseNeeded()) { 
			MessageDialog.openWarning(editor.getSite().getShell(), 
					"Bytecode", "You must save it before!");
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
		String fnameTo = path.removeLastSegments(1).append("_" + lastSegment).
		                                            toOSString();
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot(); 
		IFile fileFrom = root.getFile(new Path(fnameFrom));
		IPath pathTo = new Path(fnameTo);
		IFile fileTo = root.getFile(pathTo);
		try {
			fileTo.delete(true, null);
			fileFrom.copy(pathTo, true, null);
		} catch (CoreException e1) {
			MessageDialog.openWarning(editor.getSite().getShell(), 
					"Bytecode", "Cannot regenerate the bytecode file");
			return;
		}
		updateMethods(file, path, lastSegment);
		contributor.synchrEnable();
	}

	/**
	 * TODO
	 * 
	 * @param file
	 * @param path
	 * @param lastSegment
	 */
	private void updateMethods(IFile file, IPath path, String lastSegment) {
		try {
		String clname = path.removeFirstSegments(1).toPortableString().
		                     replaceFirst(UmbraHelper.BYTECODE_EXTENSION, "");
		ClassPath cp;
		try {
			cp = new ClassPath(getClassPath());
		} catch (JavaModelException e1) {
			MessageDialog.openWarning(editor.getSite().getShell(), 
					"Bytecode", "Classpath cannot be properly resolved, "+
					            "empty classpath is used instead");
			cp = new ClassPath("");
		}
		SyntheticRepository strin = SyntheticRepository.getInstance(cp);
		try {	
			JavaClass jc = strin.loadClass(clname);
			strin.removeClass(jc);
			JavaClass oldJc = ((BytecodeEditor)editor).getJavaClass();
			ClassGen cg = updateModifiedMethods(oldJc, jc);
			jc = cg.getJavaClass();
			BytecodeEditor bcEditor = ((BytecodeEditor)editor);
			String fullName = bcEditor.getPath(path).toOSString();
			jc.dump(fullName + UmbraHelper.getFileSeparator() + lastSegment);
			bcEditor.setJavaClass(jc);
			MessageDialog.openWarning(editor.getSite().getShell(), 
					"Bytecode", "A "+fullName + UmbraHelper.getFileSeparator() + lastSegment);
			bcEditor.refreshBytecode(path, null, null);
			MessageDialog.openWarning(editor.getSite().getShell(), 
					"Bytecode", "B");
			IEditorInput input = new FileEditorInput(file);
			MessageDialog.openWarning(editor.getSite().getShell(), 
					"Bytecode", "C");
			contributor.refreshEditor(editor, input);
			MessageDialog.openWarning(editor.getSite().getShell(), 
					"Bytecode", "D");
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
		} catch (RuntimeException re) {
			re.printStackTrace();
		}
	}

	/**
	 * This method generates the classpath for the project in which the current
	 * action takes place. 
	 * 
	 * TODO probably the entry separator should be made OS independent 
	 * 
	 * @return the string representing the claspath
	 * @throws JavaModelException 
	 */
	private String getClassPath() throws JavaModelException {
		String res = "";
		String classPathSeparator = UmbraHelper.getClassPathSeparator();
		String fileSeparator = UmbraHelper.getFileSeparator();
		IFile file = ((FileEditorInput)editor.getEditorInput()).getFile();
		String projectName = file.getFullPath().segment(0);
		IWorkspaceRoot myWorkspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
		IProject project = myWorkspaceRoot.getProject(projectName);
		IJavaProject jproject = JavaCore.create(project);
		IClasspathEntry[] ent;
		ent = jproject.getResolvedClasspath(true);
		for (int i=0; i<ent.length;i++){
			String add = "";
			// TODO replace println with the sensible code to realise the functionality
			switch (ent[i].getEntryKind()) {
			case IClasspathEntry.CPE_CONTAINER:
				System.out.println("CONTAINER: "+ent[i].getPath().
						                                toPortableString());
				break;
			case IClasspathEntry.CPE_LIBRARY:
				add=ent[i].getPath().toPortableString();
				break;
			case IClasspathEntry.CPE_PROJECT:
				System.out.println("PROJECT: "+ent[i].getPath().
						                              toPortableString());
				break;
			case IClasspathEntry.CPE_SOURCE:
				String ploc = project.getLocation().toPortableString();
				String sloc = ent[i].getPath().toPortableString();
				add=sloc.replaceFirst(fileSeparator+projectName, ploc);
				break;
			case IClasspathEntry.CPE_VARIABLE:
				add = "";
				break;
			default:
				add = "";
				break;
			}
			if (res.length()>0)
				res+=classPathSeparator+add;
			else
				res+=add;
		}
		return res;
	}

	/**
	 * This method generates a new generated class representation 
	 * (<code>ClassGen</code>) in which the methods from the class 
	 * representation in the second parameter (<code>jc</code>) are replaced 
	 * with the methods from the first parameter (<code>oldJc</code>)
	 * provided that <code>bytecodeContribution</code> regards them as
	 * modified.
	 * 
	 * @param oldJc the class from which the modifications are acquired
	 * @param jc the class for to which the modifications are added
	 * @return the class representation with added modifications
	 */
	private ClassGen updateModifiedMethods(JavaClass oldJc, JavaClass jc) {
		ClassGen oldCg = new ClassGen(oldJc);
		ClassGen cg = new ClassGen(jc);
		int oldMeths = oldCg.getMethods().length;
		int meths = cg.getMethods().length;
		boolean[] modified;
		try {
			modified = bytecodeContribution.getModified();
		} catch (NullPointerException e) {
			MessageDialog.openWarning(editor.getSite().getShell(), 
					"Bytecode", "Nothing has been modified");

			throw e;
		}
		for (int i = 0; i < modified.length && i < oldMeths && i < meths; i++) {
			if (modified[i]) {
				cg.setMethodAt(oldCg.getMethodAt(i), i);
				System.out.println(oldCg.getMethodAt(i).getCode().toString(true));
			}
		}
		return cg;
	}
	
	/**
	 * The method sets the editor for which the operation to combine
	 * the modifications in the source code and in the byte code will 
	 * be performed.
	 * 
	 * @param part the editor to combine modifications
	 */
	public void setActiveEditor(IEditorPart part) {
		editor = part;
	}
}
