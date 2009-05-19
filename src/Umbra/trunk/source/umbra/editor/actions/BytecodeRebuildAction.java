/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.actions;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.part.FileEditorInput;

import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeEditor;
import umbra.editor.BytecodeEditorContributor;
import umbra.lib.EclipseIdentifiers;
import umbra.lib.FileNames;
import umbra.lib.UmbraRepresentationException;

/**
 * This class defines action of restoring the original version
 * of a class file (it is saved with the name prefixed with '_')
 * and then generating byte code (.btc) directly from it.
 * In this way, all the changes made up to now are removed.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeRebuildAction extends BytecodeEditorAction {

  /**
   * This constructor creates the action to restore the original contents
   * of the class file. It registers the name of the action and stores
   * locally the object which creates all the actions
   * and which contributes the editor GUI elements to the eclipse GUI.
   *
   * @param a_contributor the manager that initialises all the actions within
   *   the byte code plugin
   * @param a_bytecode_contribution the GUI elements contributed to the eclipse
   *   GUI by the byte code editor. This reference should be the same as in the
   *   parameter <code>a_contributor</code>.
   */
  public BytecodeRebuildAction(final BytecodeEditorContributor a_contributor,
                         final BytecodeContribution a_bytecode_contribution) {
    super(EclipseIdentifiers.REBUILD_ACTION_NAME, a_contributor,
          a_bytecode_contribution);
  }

  /**
   * This method restores a saved copy of the original .class file that resulted
   * from the Java source file (it is stored under the name of the class file
   * prefixed with '_'). The class file with our modifications is removed, and
   * the editor input is updated together with the editor window.
   *
   */
  public final void run() {
    final Shell parent = getEditor().getSite().getShell();
    final IFile file = ((FileEditorInput)getEditor().getEditorInput()).
                                                     getFile();
    if (getEditor().getDocument() == null)
      getEditor().setDocument((BytecodeDocument)getEditor().
        getDocumentProvider().getDocument(getEditor().getEditorInput()));
    final IPath active = file.getFullPath();
    final String fnameTo =
      active.toPortableString().replaceFirst(FileNames.BYTECODE_EXTENSION,
                  FileNames.CLASS_EXTENSION);
    final String fnameFrom = FileNames.getSavedClassFileNameForBTC(active);
    final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    final IFile fileFrom = root.getFile(new Path(fnameFrom));
    final IPath pathTo = new Path(fnameTo);
    if (fileFrom.exists()) {
      replaceFile(fileFrom, pathTo);
    }
    try {
      final IPath cpath = FileNames.getClassFileFileFor(file, 
         getEditor()).getFullPath();
      ((BytecodeEditor)getEditor()).refreshBytecode(cpath,
                                  getEditor().getDocument(), null, null);
      final IEditorInput input = new FileEditorInput(file);
      getContributor().refreshEditor(getEditor(), input, null, null);
    } catch (ClassNotFoundException e1) {
      wrongPathToClassMessage(parent, getDescription(), file.toString());
    } catch (CoreException e1) {
      wrongFileOperationMessage(parent, getDescription());
    } catch (UmbraRepresentationException e) {
      wrongRepresentationMessage(parent, getDescription(), e);
    }
  }

  /**
   * The method replaces file at the path <code>pathTo</code> with the file
   * determined by <code>fileFrom</code>. This method pops up a message
   * in case the operation cannot be executed.
   *
   * @param a_filefrom a file which replaces
   * @param a_pathto a location to be replaced
   */
  private void replaceFile(final IFile a_filefrom, final IPath a_pathto) {
    final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    final Shell parent = getEditor().getSite().getShell();
    try {
      final IFile fileTo = root.getFile(a_pathto);
      fileTo.delete(true, null);
      a_filefrom.copy(a_pathto, true, null);
    } catch (CoreException e) {
      wrongFileOperationMessage(parent, getDescription());
    }
  }
}
