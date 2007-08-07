/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
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
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import umbra.UmbraPlugin;
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
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeCombineAction extends BytecodeEditorAction {

  /**
   * This constructor creates the action to combine the bytecode edits with
   * the source code ones. It registers the name of the action with the text
   * "Combine" and stores locally the object which creates all the actions
   * and which contributs the editor GUI elements to the eclipse GUI.
   *
   * @param a_contributor the manager that initialises all the actions within
   * the bytecode plugin
   * @param a_bytecode_contribution the GUI elements contributed to the eclipse
   * GUI by the bytecode editor. This reference should be the same as in the
   * parameter <code>a_contributor</code>.
   */
  public BytecodeCombineAction(final BytecodeEditorContributor a_contributor,
                 final BytecodeContribution a_bytecode_contribution) {
    super("Combine", a_contributor, a_bytecode_contribution);
  }

  /**
   * The action is similar to rebuild - it generates
   * input from the original source in the same way.
   * The difference is that after this all methods are
   * checked for bytecode modifications and if one
   * has been made, it is chosen and saved from JavaClass.
   *
   * FIXME write more description
   *
   * @see BytecodeRebuildAction
   */
  public final void run() {
    final IEditorPart my_editor = getEditor();
    final IEditorPart related = ((BytecodeEditor)my_editor).getRelatedEditor();
    if (related.isSaveOnCloseNeeded()) {
      MessageDialog.openWarning(my_editor.getSite().getShell(),
          "Bytecode", "You must save it before!");
      return;
    }
    final IFile file = ((FileEditorInput)my_editor.getEditorInput()).getFile();
    final IPath path = file.getFullPath();
    final String fnameTo = UmbraHelper.getSavedClassFileNameForBTC(path);
    final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    final String fnameFrom = path.toOSString().replaceFirst(
                  UmbraHelper.BYTECODE_EXTENSION,
                  UmbraHelper.CLASS_EXTENSION);
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
    final String lastSegment = path.lastSegment().replaceFirst(
                  UmbraHelper.BYTECODE_EXTENSION,
                  UmbraHelper.CLASS_EXTENSION);
    updateMethods(file, path, lastSegment);
    getContributor().synchrEnable();
  }

  /**
   * This method reads the Java classfile for the original Java code and
   * replaces all the methods with the ones that were modified in the currently
   * edited bytecode file. It also does all the error handling.
   *
   * FIXME this method should also pop up messages in case exceptions
   *       are thrown
   *
   * @param a_file a file edited currently by the bytecode editor
   * @param a_path a workspace relative path to a Java source code file
   * @param the_last_segment the strign which represents the last segment of
   *        the classfile file name corresponding to the file edited by the
   *        editor
   */
  private void updateMethods(final IFile a_file,
                             final IPath a_path,
                             final String the_last_segment) {
    final String clname = a_path.removeFirstSegments(1).toPortableString().
               replaceFirst(UmbraHelper.BYTECODE_EXTENSION, "");
    ClassPath cp;
    cp = new ClassPath(getClassPath());
    final SyntheticRepository strin = SyntheticRepository.getInstance(cp);
    try {
      final BytecodeEditor my_editor = (BytecodeEditor)getEditor();
      JavaClass jc = strin.loadClass(clname);
      strin.removeClass(jc);
      final JavaClass oldJc = my_editor.getJavaClass();
      final ClassGen cg = updateModifiedMethods(oldJc, jc);
      jc = cg.getJavaClass();
      final String fullName = my_editor.getPath(a_path).toOSString();
      jc.dump(fullName + UmbraHelper.getFileSeparator() + the_last_segment);
      my_editor.setJavaClass(jc);
      my_editor.refreshBytecode(a_path, null, null);
      final IEditorInput input = new FileEditorInput(a_file);
      getContributor().refreshEditor(my_editor, input);
    } catch (ClassNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    } catch (CoreException e) {
      e.printStackTrace();
    }
  }

  /**
   * This method generates the classpath for the project in which the current
   * action takes place. In case the classpath cannot be retrieved an
   * appropriate message is shown to the user and the classpath is set to
   * be the empty string.
   *
   * @return the string representing the claspath
   */
  private String getClassPath() {
    final IEditorPart my_editor = getEditor();
    final IFile file = ((FileEditorInput)my_editor.getEditorInput()).getFile();
    final String projectName = file.getFullPath().segment(0);
    final IWorkspaceRoot myWorkspaceRoot = ResourcesPlugin.getWorkspace().
                                                           getRoot();
    final IProject project = myWorkspaceRoot.getProject(projectName);
    final IJavaProject jproject = JavaCore.create(project);
    IClasspathEntry[] ent;
    try {
      ent = jproject.getResolvedClasspath(true);
    } catch (JavaModelException e) {
      MessageDialog.openWarning(my_editor.getSite().getShell(),
                      "Bytecode", "Classpath cannot be properly resolved, " +
                      "empty classpath is used instead");
      return "";
    }
    return classPathEntriesToString(ent, project, projectName);
  }

  /**
   * The method retruns a string representation of a classpath the entries
   * of which are in the parameter <code>the_entries</code> and which
   * is associated with the project <code>a_project</code>. The
   * <code>a_project_name</code> parameter is here for efficiency reasons.
   *
   * @param the_entries the entries of the classpath
   * @param a_project the project with the classpath
   * @param a_project_name the name of the project with the classpath
   *
   * @return the string representation of the classpath entries
   */
  private String classPathEntriesToString(final IClasspathEntry[] the_entries,
                                          final IProject a_project,
                                          final String a_project_name) {
    final String classPathSeparator = UmbraHelper.getClassPathSeparator();
    final String fileSeparator = UmbraHelper.getFileSeparator();
    String res = "";
    for (int i = 0; i < the_entries.length; i++) {
      String add = "";
      // FIXME replace println with the sensible code to realise the
      //       functionality
      switch (the_entries[i].getEntryKind()) {
        case IClasspathEntry.CPE_CONTAINER:
          UmbraPlugin.messagelog("CONTAINER: " + the_entries[i].getPath().
                             toPortableString());
          break;
        case IClasspathEntry.CPE_LIBRARY:
          add = the_entries[i].getPath().toPortableString();
          break;
        case IClasspathEntry.CPE_PROJECT:
          UmbraPlugin.messagelog("PROJECT: " + the_entries[i].getPath().
                             toPortableString());
          break;
        case IClasspathEntry.CPE_SOURCE:
          final String ploc = a_project.getLocation().toPortableString();
          final String sloc = the_entries[i].getPath().toPortableString();
          add = sloc.replaceFirst(fileSeparator + a_project_name, ploc);
          break;
        case IClasspathEntry.CPE_VARIABLE:
          add = "";
          break;
        default:
          add = "";
          break;
      }
      if (res.length() > 0) {
        res += classPathSeparator + add;
      } else {
        res += add;
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
   * @param an_old_jc the class from which the modifications are acquired
   * @param a_jc the class for to which the modifications are added
   * @return the class representation with added modifications
   */
  private ClassGen updateModifiedMethods(final JavaClass an_old_jc,
                       final JavaClass a_jc) {
    final ClassGen oldCg = new ClassGen(an_old_jc);
    final ClassGen cg = new ClassGen(a_jc);
    final int oldMeths = oldCg.getMethods().length;
    final int meths = cg.getMethods().length;
    boolean[] modified;
    try {
      modified = getContribution().getModified();
    } catch (NullPointerException e) {
      MessageDialog.openWarning(getEditor().getSite().getShell(),
          "Bytecode", "Nothing has been modified");

      throw e;
    }
    for (int i = 0; i < modified.length && i < oldMeths && i < meths; i++) {
      if (modified[i]) {
        cg.setMethodAt(oldCg.getMethodAt(i), i);
        UmbraPlugin.messagelog(oldCg.getMethodAt(i).getCode().toString(true));
      }
    }
    return cg;
  }

}
