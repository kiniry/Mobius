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
 * @author Wojtek Wąs (wojtekwas@poczta.onet.pl)
 * @version a-01
 */
public class BytecodeCombineAction extends Action {

  /**
   * The current bytecode editor for which the action takes place.
   */
  private IEditorPart my_editor;

  /**
   * The manager that initialises all the actions within the
   * bytecode plugin.
   */
  private BytecodeEditorContributor my_contributor;

  /**
   * TODO should be the same as in my_contributor
   */
  private BytecodeContribution my_btcodeCntrbtn;
  //@ invariant my_contributor.bytecodeContribution==my_btcodeCntrbtn;

  /**
   * TODO
   *
   * @param a_contributor
   * @param a_bytecode_contribution
   */
  public BytecodeCombineAction(final BytecodeEditorContributor a_contributor,
                 final BytecodeContribution a_bytecode_contribution) {
    super("Combine");
    this.my_contributor = a_contributor;
    this.my_btcodeCntrbtn = a_bytecode_contribution;
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
  public final void run() {
    final IEditorPart related = ((BytecodeEditor)my_editor).getRelatedEditor();
    if (related.isSaveOnCloseNeeded()) {
      MessageDialog.openWarning(my_editor.getSite().getShell(),
          "Bytecode", "You must save it before!");
      return;
    }
    final IFile file = ((FileEditorInput)my_editor.getEditorInput()).getFile();
    final IPath path = file.getFullPath();
    final String fnameFrom = path.toOSString().replaceFirst(
                  UmbraHelper.BYTECODE_EXTENSION,
                  UmbraHelper.CLASS_EXTENSION);
    final String lastSegment = path.lastSegment().replaceFirst(
                  UmbraHelper.BYTECODE_EXTENSION,
                  UmbraHelper.CLASS_EXTENSION);
    final String fnameTo = path.removeLastSegments(1).append("_" + lastSegment).
                          toOSString();
    final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    final IFile fileFrom = root.getFile(new Path(fnameFrom));
    final IPath pathTo = new Path(fnameTo);
    final IFile fileTo = root.getFile(pathTo);
    try {
      fileTo.delete(true, null);
      fileFrom.copy(pathTo, true, null);
    } catch (CoreException e1) {
      MessageDialog.openWarning(my_editor.getSite().getShell(),
          "Bytecode", "Cannot regenerate the bytecode file");
      return;
    }
    updateMethods(file, path, lastSegment);
    my_contributor.synchrEnable();
  }

  /**
   * TODO
   *
   * @param a_file
   * @param a_path
   * @param the_lastSegment
   */
  private void updateMethods(final IFile a_file,
                             final IPath a_path,
                             final String the_lastSegment) {
    try {
      final String clname = a_path.removeFirstSegments(1).toPortableString().
               replaceFirst(UmbraHelper.BYTECODE_EXTENSION, "");
      ClassPath cp;
      try {
        cp = new ClassPath(getClassPath());
      } catch (JavaModelException e1) {
        MessageDialog.openWarning(my_editor.getSite().getShell(),
                     "Bytecode", "Classpath cannot be properly resolved, " +
                     "empty classpath is used instead");
        cp = new ClassPath("");
      }
      final SyntheticRepository strin = SyntheticRepository.getInstance(cp);
      try {
        JavaClass jc = strin.loadClass(clname);
        strin.removeClass(jc);
        final JavaClass oldJc = ((BytecodeEditor)my_editor).getJavaClass();
        final ClassGen cg = updateModifiedMethods(oldJc, jc);
        jc = cg.getJavaClass();
        final BytecodeEditor bcEditor = ((BytecodeEditor)my_editor);
        final String fullName = bcEditor.getPath(a_path).toOSString();
        jc.dump(fullName + UmbraHelper.getFileSeparator() + the_lastSegment);
        bcEditor.setJavaClass(jc);
        MessageDialog.openWarning(my_editor.getSite().getShell(),
          "Bytecode", "A " + fullName + UmbraHelper.getFileSeparator() + 
                             the_lastSegment);
        bcEditor.refreshBytecode(a_path, null, null);
        MessageDialog.openWarning(my_editor.getSite().getShell(),
          "Bytecode", "B");
        final IEditorInput input = new FileEditorInput(a_file);
        MessageDialog.openWarning(my_editor.getSite().getShell(),
          "Bytecode", "C");
        my_contributor.refreshEditor(my_editor, input);
        MessageDialog.openWarning(my_editor.getSite().getShell(),
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
    final String classPathSeparator = UmbraHelper.getClassPathSeparator();
    final String fileSeparator = UmbraHelper.getFileSeparator();
    final IFile file = ((FileEditorInput)my_editor.getEditorInput()).getFile();
    final String projectName = file.getFullPath().segment(0);
    final IWorkspaceRoot myWorkspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
    final IProject project = myWorkspaceRoot.getProject(projectName);
    final IJavaProject jproject = JavaCore.create(project);
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
        final String ploc = project.getLocation().toPortableString();
        final String sloc = ent[i].getPath().toPortableString();
        add=sloc.replaceFirst(fileSeparator+projectName, ploc);
        break;
      case IClasspathEntry.CPE_VARIABLE:
        add = "";
        break;
      default:
        add = "";
        break;
      }
      if (res.length()>0) {
        res+=classPathSeparator+add;
      } else {
        res+=add;
      }
    }
    return res;
  }

  /**
   * This method generates a new generated class representation
   * (<code>ClassGen</code>) in which the methods from the class
   * representation in the second parameter (<code>jc</code>) are replaced
   * with the methods from the first parameter (<code>oldJc</code>)
   * provided that <code>my_btcodeCntrbtn</code> regards them as
   * modified.
   *
   * @param an_oldJc the class from which the modifications are acquired
   * @param a_jc the class for to which the modifications are added
   * @return the class representation with added modifications
   */
  private ClassGen updateModifiedMethods(final JavaClass an_oldJc,
                       final JavaClass a_jc) {
    final ClassGen oldCg = new ClassGen(an_oldJc);
    final ClassGen cg = new ClassGen(a_jc);
    final int oldMeths = oldCg.getMethods().length;
    final int meths = cg.getMethods().length;
    boolean[] modified;
    try {
      modified = my_btcodeCntrbtn.getModified();
    } catch (NullPointerException e) {
      MessageDialog.openWarning(my_editor.getSite().getShell(),
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
  public final void setActiveEditor(final IEditorPart part) {
    my_editor = part;
  }
}
