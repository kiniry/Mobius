/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;

import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeEditor;
import umbra.editor.BytecodeEditorContributor;
import umbra.lib.UmbraLocationException;

/**
 * This class defines the common operations for all the byte code editor
 * actions. It is responsible for accessing the editor, contributor,
 * and contribution. Except for that it contains the methods to display
 * messages when errors occur.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class BytecodeEditorAction extends Action {

  /**
   * The current byte code editor for which the action takes place.
   */
  private BytecodeEditor my_editor;

  /**
   * The manager that initialises all the actions within the
   * byte code plugin.
   */
  private BytecodeEditorContributor my_contributor;

  /**
   * The GUI elements contributed to the eclipse GUI by the bytecode
   * editor. This reference should be the same as in the field
   * <code>my_contributor</code>.
   */
  private BytecodeContribution my_btcodeCntrbtn;
  //@ invariant my_contributor.bytecodeContribution==my_btcodeCntrbtn;

  /**
   * This constructor creates the generic part of a byte code editor action.
   * It registers the action under the title given by <code>a_name</code>
   * parameter and stores locally the object which creates all the actions
   * and which contributes the editor GUI elements to the eclipse GUI.
   *
   * @param a_name a name of the action to register
   * @param a_contributor the manager that initialises all the actions within
   *   the byte code plugin
   * @param a_bytecode_contribution the GUI elements contributed to the eclipse
   *   GUI by the byte code editor. This reference should be the same as in the
   *   parameter <code>a_contributor</code>.
   */
  public BytecodeEditorAction(final String a_name,
                          final BytecodeEditorContributor a_contributor,
                          final BytecodeContribution a_bytecode_contribution) {
    super(a_name);
    my_contributor = a_contributor;
    my_btcodeCntrbtn = a_bytecode_contribution;
  }


  /**
   * The method sets the bytecode editor for which the operation will
   * be performed.
   *
   * @param a_part the bytecode editor to perform the operations
   */
  public void setActiveEditor(final IEditorPart a_part) {
    my_editor = (BytecodeEditor)a_part;
  }

  /**
   * @return the bytecode editor currently associated with the action
   */
  public final BytecodeEditor getEditor() {
    return my_editor;
  }

  /**
   * @return the manager that initialises all the bytecode actions in the plugin
   */
  public final BytecodeEditorContributor getContributor() {
    return my_contributor;
  }

  /**
   * @return the objects that encapsulates the GUI elements contributed by the
   * bytecode plugin
   */
  public final BytecodeContribution getContribution() {
    return my_btcodeCntrbtn;
  }

  /**
   * Displays the message that a wrong location has been reached.
   *
   * @param a_shell the shell which displays the message
   * @param a_title the title of the message window
   * @param an_ex the exception with the information to display
   */
  public static void wrongLocationMessage(final Shell a_shell,
                                          final String a_title,
                                          final UmbraLocationException an_ex) {
    MessageDialog.openError(a_shell,
                            a_title,
                            "Wrong location " + an_ex.getWrongLocation() +
                            " in a " +
                            (an_ex.isByteCodeDocument() ? "byte code" :
                                                    "Java") +
                            "document");
  }

  /**
   * Displays the message that a file operation on a class file failed.
   *
   * @param a_shell the shell which displays the message
   * @param a_title the title of the message window
   */
  public static void wrongFileOperationMessage(final Shell a_shell,
                                               final String a_title) {
    MessageDialog.openError(a_shell,
                            a_title,
                            "A file operation on the class file failed");
  }

  /**
   * Displays the message that a given path does not lead to a valid class
   * file.
   *
   * @param a_shell the shell which displays the message
   * @param a_title the title of the message window
   * @param a_path a path which was referenced
   */
  public static void wrongPathToClassMessage(final Shell a_shell,
                                       final String a_title,
                                       final String a_path) {
    MessageDialog.openError(a_shell,
                            a_title,
                            "The path " + a_path +
                            " does not lead to a valid class file");
  }


  /**
   * Displays the message that the current project has no output path for
   * Java class files.
   *
   * @param a_shell the shell which displays the message
   * @param a_title the title of the message window
   */
  public static void wrongClassFileOptMessage(final Shell a_shell,
                                              final String a_title) {
    MessageDialog.openError(a_shell,
                          a_title,
                          "No class file output path for Java files is set");
  }
}
