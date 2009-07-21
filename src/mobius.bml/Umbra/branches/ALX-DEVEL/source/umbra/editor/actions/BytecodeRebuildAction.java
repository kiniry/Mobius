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
import org.eclipse.jface.action.Action;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import umbra.editor.BytecodeEditor;
import umbra.editor.BytecodeEditorContributor;

/**
 * This class defines action of restoring the original version
 * of a classfile (it is saved with the name prefixed with '_')
 * and then generating bytecode (.btc) directly from it.
 * In this way, all the changes made up to now are removed.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeRebuildAction extends Action {

  /**
   * The current bytecode editor for which the action takes place.
   */
  private BytecodeEditor my_editor;

  /**
   * The manager that initialises all the actions within the
   * bytecode plugin.
   */
  private BytecodeEditorContributor my_contributor;

  /**
   * This constructor creates the action to restore the original contents
   * of the classfile. It registers the name of the action with the text
   * "Rebuild" and stores locally the object which creates all the actions
   * and which contributs the editor GUI elements to the eclipse GUI.
   *
   * @param a_contributor the manager that initialises all the actions within
   * the bytecode plugin
   */
  public BytecodeRebuildAction(final BytecodeEditorContributor a_contributor) {
    super("Rebuild");
    this.my_contributor = a_contributor;
  }

  /**
   * This method sets the bytecode editor for which the
   * rebuild action will be executed.
   *
   * @param a_target_editor the bytecode editor for which the action will be
   *    executed
   */
  public final void setActiveEditor(final IEditorPart a_target_editor) {
    my_editor = (BytecodeEditor)a_target_editor;
  }

  /**
   * This method restores a saved copy of the original .class file that resulted
   * from the Java source file (it is stored under the name of the classfile
   * prefixed with '_'). The classfile with our modifications is removed, and
   * the editor input is updated together with the editor window.
   *
   */
  public final void run() {
    final IFile file = ((FileEditorInput)my_editor.getEditorInput()).getFile();
    final IPath active = file.getFullPath();
    final String fnameTo = active.toPortableString().replaceFirst(
                  UmbraHelper.BYTECODE_EXTENSION,
                  UmbraHelper.CLASS_EXTENSION);
    final String fnameFrom = UmbraHelper.getSavedClassFileNameForBTC(active);
    final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    final IFile fileFrom = root.getFile(new Path(fnameFrom));
    final IPath pathTo = new Path(fnameTo);
    final IFile fileTo = root.getFile(pathTo);
    if (fileFrom.exists()) {
      try {
        fileTo.delete(true, null);
        fileFrom.copy(pathTo, true, null);
      } catch (CoreException e) {
        e.printStackTrace();
      }
    }
    try {
      ((BytecodeEditor)my_editor).refreshBytecode(active, null, null);
      final IEditorInput input = new FileEditorInput(file);
      my_contributor.refreshEditor(my_editor, input);
    } catch (ClassNotFoundException e1) {
      e1.printStackTrace();
    } catch (CoreException e1) {
      e1.printStackTrace();
    }
    my_contributor.synchrEnable();
  }
}
