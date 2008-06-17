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
 * This class defines an action that adds current byte code snapshot
 * to the history stack. The stack is implemented in the file system.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class HistoryAction extends BytecodeEditorAction {

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
  public HistoryAction(final BytecodeEditorContributor a_contributor,
                       final BytecodeContribution a_btcd_contribution) {
    super(EclipseIdentifiers.HISTORY_ACTION_NAME, a_contributor,
          a_btcd_contribution);
  }

  /**
   * This method increments the counter of the existing history snapshots.
   * In case the history stack is full an appropriate message is
   * displayed. Otherwise, the files for the currently edited bytecode
   * file (i.e. .btc file and .class file) are saved into the history.
   *
   */
  public final void run() {
    final int num = (getEditor()).newHistory();
    if (num == -1) {
      MessageDialog.openInformation(getEditor().getEditorSite().getShell(),
        getDescription(), GUIMessages.HISTORY_FULL_MESSAGE);
      return;
    }

    final IFile fileFrom = ((FileEditorInput)getEditor().getEditorInput()).
                                                         getFile();
    try {
      HistoryOperations.saveBTCHistoryFile(fileFrom, num,
                                           getEditor().getRelatedEditor());
      HistoryOperations.saveClassHistoryFile(fileFrom, num,
                                             getEditor().getRelatedEditor());
    } catch (CoreException e) {
      final Shell parent = getEditor().getSite().getShell();
      MessageDialog.openError(parent, getDescription(),
                              GUIMessages.FAILED_CLASS_FILE_OPERATION);
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
