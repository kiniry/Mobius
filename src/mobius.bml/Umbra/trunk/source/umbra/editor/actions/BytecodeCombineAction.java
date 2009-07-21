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
import org.eclipse.core.internal.resources.ResourceException;
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
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeEditor;
import umbra.editor.BytecodeEditorContributor;
import umbra.instructions.BytecodeController;
import umbra.lib.BMLParsing;
import umbra.lib.EclipseIdentifiers;
import umbra.lib.FileNames;
import umbra.lib.GUIMessages;
import umbra.lib.UmbraClassException;
import umbra.lib.UmbraRepresentationException;
import annot.bcclass.BCClass;
import annot.io.ReadAttributeException;

/**
 * This is an action associated with a byte code editor (an
 * extension .btc). The action allows linking changes
 * made to byte code with the ones made to the source Java code.
 * The current implementation works only when the changes are
 * made to different methods. In case a modification happens in the
 * same method, the byte code modification is privileged.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeCombineAction extends BytecodeEditorAction {

  /**
   * This constructor creates the action to combine the byte code edits with
   * the source code ones. It registers the name of the action and stores
   * locally the object which creates all the actions
   * and which contributes the editor GUI elements to the eclipse GUI.
   *
   * @param a_contributor the manager that initialises all the actions within
   *   the byte code plugin
   * @param a_bytecode_contribution the GUI elements contributed to the eclipse
   *   GUI by the byte code editor. This reference should be the same as in the
   *   parameter <code>a_contributor</code>.
   */
  public BytecodeCombineAction(final BytecodeEditorContributor a_contributor,
                 final BytecodeContribution a_bytecode_contribution) {
    super(EclipseIdentifiers.COMBINE_ACTION_NAME, a_contributor,
          a_bytecode_contribution);
  }

  /**
   * This action combines the modifications that were made in the source code
   * file with the modifications in the byte code. This method checks first if
   * both source code and byte code files are saved. If so then it restores a
   * clean backup copy of the class file which does not contain the changes
   * introduced in the byte code editor. Then the method reads the
   * resulting class file and replaces all the methods with the ones that are
   * marked as modified in the Umbra structures corresponding to the currently
   * edited byte code file. The method does all the error handling.
   *
   */
  public final void run() {
    final IEditorPart related = ((BytecodeEditor)getEditor()).
                                             getRelatedEditor();
    if (related.isDirty() && getEditor().isDirty()) {
      MessageDialog.openWarning(getEditor().getSite().getShell(),
          getDescription(), GUIMessages.SAVE_BYTECODE_AND_SOURCE_FIRST);
      return;
    }
    final IFile file = ((FileEditorInput)getEditor().getEditorInput()).
                                                     getFile();
    final IPath path = file.getFullPath();
    final String fnameTo = FileNames.getSavedClassFileNameForBTC(path);
    final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    final String fnameFrom = path.toOSString().replaceFirst(
                  FileNames.BYTECODE_EXTENSION,
                  FileNames.CLASS_EXTENSION);
    final IFile fileFrom = root.getFile(new Path(fnameFrom));
    final IPath pathTo = new Path(fnameTo);
    final IFile fileTo = root.getFile(pathTo);
    try {
      fileTo.delete(true, null);
      fileFrom.copy(pathTo, true, null);
    } catch (CoreException e1) {
      wrongFileOperationMessage(getEditor().getSite().getShell(),
                                getDescription());
      return;
    }
    final String lastSegment = path.lastSegment().replaceFirst(
                  FileNames.BYTECODE_EXTENSION,
                  FileNames.CLASS_EXTENSION);
    updateMethods(file, path, lastSegment);
  }

  /**
   * This method reads the Java classfile for the original Java code and
   * replaces all the methods with the ones that were modified in the currently
   * edited byte code file. It also does all the error handling.
   *
   * @param a_file a file edited currently by the byte code editor
   * @param a_path a workspace relative path to a Java source code file
   * @param the_last_segment the string which represents the last segment of
   *        the class file file name corresponding to the file edited by the
   *        editor
   */
  private void updateMethods(final IFile a_file,
                             final IPath a_path,
                             final String the_last_segment) {
    final Shell parent = getEditor().getSite().getShell();
    final String clname = a_path.removeFirstSegments(1).toPortableString().
               replaceFirst(FileNames.BYTECODE_EXTENSION, "");
    ClassPath cp;
    cp = new ClassPath(getClassPath());
    final SyntheticRepository strin = SyntheticRepository.getInstance(cp);
    try {
      updateMethodsLogic(a_file, a_path, the_last_segment, clname, strin);
    } catch (UmbraClassException e) {
      final Exception e1 = e.getCause();
      if (e1 instanceof ClassNotFoundException) {
        wrongPathToClassMessage(parent, getDescription(), clname);
      } else if (e1 instanceof ReadAttributeException) {
        wrongBMLAttribute(parent, getDescription());
      }
    } catch (CoreException e) {
      wrongFileOperationMessage(parent, getDescription());
    } catch (UmbraRepresentationException e) {
      wrongRepresentationMessage(parent, getDescription(), e);
    }
  }

  /**
   * This method contains the logic of the merging together the byte code that
   * comes from the source code manipulations and byte code manipulations. The
   * method loads the class <code>a_clname</code> from the repository described
   * in <code>a_repo</code>. It retrieves from the editor internal structures
   * the local representation of the modified class and updates the
   * representation with the content of the class file which is the result of
   * the source code compilation. The result of this operation is stored
   * in the file the name of which is the path <code>a_path</code> followed by
   * the directory separator, followed by the file name
   * <code>the_last_segment</code>. Finally, the current byte code editor is
   * refreshed with the content of the newly generated file.
   *
   * @param a_file a file resource which is associated to the document for
   *   which the current combine action is executed
   * @param a_path the path to the location where the resulting file should
   *   be stored
   * @param the_last_segment the last segment of a file path (a file name)
   *   to which the new content should be generated; it is a class file name
   * @param a_clname the name of the class to update the content for
   * @param a_repo the repository to load the class file from
   *
   * @throws CoreException in case I/O operations on a class file failed
   * @throws UmbraClassException in case the class for the given name cannot
   *   be found in the given class path repository or in case the parsing of
   *   the BML attributes in the class file failed
   * @throws UmbraRepresentationException in case the internal representation
   *   of the bytecode text cannot be initialised
   * @throws UmbraClassException the class corresponding to the given path
   *   cannot be found
   */
  private void updateMethodsLogic(final IFile a_file,
                                  final IPath a_path,
                                  final String the_last_segment,
                                  final String a_clname,
                                  final SyntheticRepository a_repo)
    throws CoreException, UmbraRepresentationException, UmbraClassException {
    final BytecodeEditor my_editor = (BytecodeEditor)getEditor();
    JavaClass jc;
    try {
      jc = a_repo.loadClass(a_clname);
    } catch (ClassNotFoundException e1) {
      throw new UmbraClassException(e1);
    }
    a_repo.removeClass(jc);
    final ClassGen oldJc = my_editor.getDocument().getJavaClass();
    final ClassGen cg = updateModifiedMethods(oldJc, jc);
    jc = cg.getJavaClass();
    final String fullName = FileNames.getPath(a_path).toOSString();
    try {
      jc.dump(fullName + FileNames.getFileSeparator() + the_last_segment);
    } catch (IOException e) {
      throw new ResourceException(1, a_path, "The class file cannot be dumped",
                                  e);
    }
    try {
      my_editor.refreshBytecode(a_path, my_editor.getDocument(), null, null);
    } catch (ClassNotFoundException e1) {
      throw new UmbraClassException(e1);
    }
    refreshEditorWithClass(a_file, my_editor, jc);
  }

  /**
   * The method does the refresh operation for the current editor in such a
   * way that the given file and class are associated with the edited document.
   *
   * @param a_file a class file to associate with the editor
   * @param an_editor to associate the file and the class to
   * @param a_jc a class file representation to associate to the editor
   * @throws UmbraClassException in case the parsing of
   *   the BML attributes in the class file failed
   * @throws PartInitException if the new editor could not be created or
   *    initialised
   * @throws UmbraRepresentationException in case the internal representation
   *   of the bytecode text cannot be initialised
   */
  private void refreshEditorWithClass(final IFile a_file,
                                      final BytecodeEditor an_editor,
                                      final JavaClass a_jc)
    throws UmbraClassException, PartInitException,
           UmbraRepresentationException {
    BCClass bcc;
    try {
      bcc = new BCClass(a_jc);
    } catch (ReadAttributeException e1) {
      throw new UmbraClassException(e1);
    }
    //note that BMLParsing object is initialised with help of the BCClass
    final BMLParsing bmlp = new BMLParsing(bcc);
    an_editor.getDocument().setEditor(an_editor, bmlp);
    final IEditorInput input = new FileEditorInput(a_file);
    getContributor().refreshEditor(an_editor, input, null, null);
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
        getDescription(), GUIMessages.CLASSPATH_PROBLEMS_MESSAGE);
      return "";
    }
    return classPathEntriesToString(ent, project, projectName);
  }

  /**
   * The method returns a string representation of a classpath the entries
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
    final String classPathSeparator = FileNames.getClassPathSeparator();
    final String fileSeparator = FileNames.getFileSeparator();
    String res = "";
    for (int i = 0; i < the_entries.length; i++) {
      String add = "";
      switch (the_entries[i].getEntryKind()) {
        case IClasspathEntry.CPE_CONTAINER:
          add = the_entries[i].getPath().toPortableString();
          break; // TODO: maybe different
        case IClasspathEntry.CPE_LIBRARY:
          add = the_entries[i].getPath().toPortableString();
          break; // TODO: maybe different
        case IClasspathEntry.CPE_PROJECT:
          add = the_entries[i].getPath().toPortableString();
          break;
        case IClasspathEntry.CPE_SOURCE:
          final String ploc = a_project.getLocation().toPortableString();
          final String sloc = the_entries[i].getPath().toPortableString();
          add = sloc.replaceFirst(fileSeparator + a_project_name, ploc);
          break;
        case IClasspathEntry.CPE_VARIABLE:
          add = "";
          break; // TODO: maybe different
        default:
          add = "";
          break; // TODO: maybe different
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
   * @param oldCg the class from which the modifications are acquired
   * @param a_jc the class for to which the modifications are added
   * @return the class representation with added modifications
   */
  private ClassGen updateModifiedMethods(final ClassGen oldCg,
                       final JavaClass a_jc) {
    final ClassGen cg = new ClassGen(a_jc);
    final int oldMeths = oldCg.getMethods().length;
    final int meths = cg.getMethods().length;
    boolean[] modified;
    try {
      final BytecodeController  model = getEditor().getDocument().getModel();
      modified = model.getModified();
    } catch (NullPointerException e) {
      MessageDialog.openError(getEditor().getSite().getShell(),
          getDescription(), GUIMessages.NOTHING_MODIFIED);
      throw e;
    }
    for (int i = 0; i < modified.length && i < oldMeths && i < meths; i++) {
      if (modified[i]) {
        cg.setMethodAt(oldCg.getMethodAt(i), i);
      }
    }
    return cg;
  }

}
