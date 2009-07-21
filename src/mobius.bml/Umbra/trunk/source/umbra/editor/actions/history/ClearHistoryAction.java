/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.actions.history;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.part.FileEditorInput;

import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeEditorContributor;
import umbra.editor.actions.BytecodeEditorAction;
import umbra.lib.EclipseIdentifiers;
import umbra.lib.GUIMessages;
import umbra.lib.HistoryOperations;

/**
 * The bytecode editor action that removes all the historical versions of code.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class ClearHistoryAction  extends BytecodeEditorAction {

  /**
   * This constructor creates the action to add item to the history
   * of the byte code editor. It registers the name of the action and stores
   * locally the object which creates all the
   * actions and which contributs the editor GUI elements to the eclipse GUI.
   *
   * @param a_contributor the manager that initialises all the actions within
   *   the bytecode plugin
   * @param a_btcd_contribution the GUI elements contributed to the eclipse
   *   GUI by the bytecode editor. This reference should be the same as in the
   *   parameter <code>a_contributor</code>.
   */
  public ClearHistoryAction(final BytecodeEditorContributor a_contributor,
                          final BytecodeContribution a_btcd_contribution) {
    super(EclipseIdentifiers.CLEAR_HISTORY_ACTION_NAME, a_contributor,
          a_btcd_contribution);
  }

  /**
   * This method clears the history for the currently active editor.
   * It resets the counter of the historical versions and then
   * deletes all the files in the workspace that represent the
   * historical versions of the current file.
   */
  public final void run() {
    getEditor().clearHistory();
    final IFile btcFile = ((FileEditorInput)getEditor().getEditorInput()).
                          getFile();
    final CompilationUnitEditor editor = getEditor().getRelatedEditor();
    for (int i = HistoryOperations.MIN_HISTORY;
         i <= HistoryOperations.MAX_HISTORY; i++) {
      try {
        HistoryOperations.removeBTCHistoryFile(btcFile, i, editor);
        HistoryOperations.removeClassHistoryFile(btcFile, i, editor);
      } catch (CoreException e) {
        final Shell parent = getEditor().getSite().getShell();
        MessageDialog.openError(parent, getDescription(),
                                GUIMessages.FAILED_CLASS_FILE_OPERATION);
      }
    }
  }

  /**
   * The method reacts when the selected area changes in the bytecode
   * editor. Currently, it does nothing.
   *
   * @param an_action the action which triggered the selection change
   * @param a_selection the new selection.
   */
  public void selectionChanged(final IAction an_action,
                               final ISelection a_selection) {
  }
}
