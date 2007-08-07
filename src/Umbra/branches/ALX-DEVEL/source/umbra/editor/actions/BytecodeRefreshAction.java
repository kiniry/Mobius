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
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;

import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeEditor;
import umbra.editor.BytecodeEditorContributor;


/**
 * This is a class defining an action: save current bytecode
 * editor window and re-generate Bytecode from BCEL structures.
 * This action is equal to generating bytecode again from the
 * Java code after saving binary file.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeRefreshAction extends BytecodeEditorAction {

  /**
   * This constructor creates the action to refresh the bytecode editor.
   * It registers the name of the action with the text "Refresh" and stores
   * locally the object which creates all the actions and which contributs
   * the editor GUI elements to the eclipse GUI.
   *
   * @param a_contributor the manager that initialises all the actions within
   * the bytecode plugin
   * @param a_bytecode_contribution the GUI elements contributed to the eclipse
   * GUI by the bytecode editor. This reference should be the same as in the
   * parameter <code>a_contributor</code>.
   */
  public BytecodeRefreshAction(final BytecodeEditorContributor a_contributor,
                 final BytecodeContribution a_bytecode_contribution) {
    super("Refresh", a_contributor, a_bytecode_contribution);
  }

  /**
   * This method sets the bytecode editor for which the refresh action will
   * be executed.
   *
   * @param a_target_editor the bytecode editor for which the action will be
   *           executed
   */
  public final void setActiveEditor(final IEditorPart a_target_editor) {
    super.setActiveEditor(a_target_editor);
    if (!getEditor().isDirty()) setEnabled(false);
  }

  /**
   * This method saves the editor content in the file associated with it
   * and then creates new input from the JavaClass structure in BCEL.
   * Finally replaces content of the editor window with the newly generated
   * input. The general idea is that the current modifications are stored
   * in a file and then retrieved back to the editor to obtain a nicely
   * formatted presentation of the code.
   */
  public final void run() {
    final BytecodeEditor my_editor = getEditor();
    final BytecodeContribution my_btcodeCntrbtn = getContribution();
    final BytecodeEditorContributor my_contributor = getContributor();
    my_editor.doSave(null);
    final IFile file = ((FileEditorInput)my_editor.getEditorInput()).getFile();
    final IPath active = file.getFullPath();
    try {
      final String[] commentTab = my_btcodeCntrbtn.getCommentTab();
      final String[] interlineTab = my_btcodeCntrbtn.getInterlineTab();
      my_editor.refreshBytecode(active, commentTab, interlineTab);
      final FileEditorInput input = new FileEditorInput(file);
      final boolean[] modified = my_btcodeCntrbtn.getModified();
      my_btcodeCntrbtn.setModTable(modified);
      my_contributor.refreshEditor(my_editor, input);
    } catch (ClassNotFoundException e) {
      e.printStackTrace();
    } catch (CoreException e) {
      e.printStackTrace();
    }
    my_contributor.synchrEnable();
  }
}
