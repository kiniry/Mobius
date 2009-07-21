/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.actions.history;

import javax.swing.JOptionPane;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.part.FileEditorInput;

import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeEditor;
import umbra.editor.BytecodeEditorContributor;
import umbra.editor.actions.BytecodeEditorAction;
import umbra.instructions.BytecodeController;
import umbra.lib.EclipseIdentifiers;
import umbra.lib.FileNames;
import umbra.lib.GUIMessages;
import umbra.lib.HistoryOperations;
import umbra.lib.UmbraRepresentationException;

/**
 * This class defines action of restoring byte code from
 * history. Current version is replaced with one of these
 * kept in history as a file with bt1, bt2, etc. extensions.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeRestoreAction extends BytecodeEditorAction {

  /**
   * This constructor creates the action to restore a file stored in the history
   * of the bytecode editor. It registers the name of the action and stores
   * locally the object which creates all the actions
   * and which contributes the editor GUI elements to the eclipse GUI.
   *
   * @param a_contributor the manager that initialises all the actions within
   *   the bytecode plugin
   * @param a_btcd_contribution the GUI elements contributed to the eclipse
   *   GUI by the bytecode editor. This reference should be the same as in the
   *   parameter <code>a_contributor</code>.
   */
  public BytecodeRestoreAction(final BytecodeEditorContributor a_contributor,
                 final BytecodeContribution a_btcd_contribution) {
    super(EclipseIdentifiers.RESTORE_ACTION_NAME, a_contributor,
          a_btcd_contribution);
  }

  /**
   * This method prompts the user for a history item number and restores the
   * corresponding history item.
   * An input dialog to insert number of version to restore is shown.
   * Then the current working class file name is established and corresponding
   * .btc history file is loaded and .class file is loaded. At last the
   * content of the .btc file is refreshed and the synchronisation action
   * is enabled. In case an error is encountered, an appropriate message
   * is displayed.
   */
  public final void run() {
    final int num = getHistoryNum();
    final BytecodeEditor editor = (BytecodeEditor)getEditor();
    final IFile btcFile = ((FileEditorInput)editor.getEditorInput()).getFile();
    final Shell parent = getEditor().getSite().getShell();
    IFile a_classfile;
    try {
      a_classfile = FileNames.getClassFileFileFor(btcFile,
                                             editor.getRelatedEditor());
    } catch (JavaModelException e2) {
      GUIMessages.wrongClassFileOptMessage(parent, getDescription());
      return;
    }
    try {
      HistoryOperations.loadBTCHistoryFile(btcFile, num,
                                           getEditor().getRelatedEditor());
      HistoryOperations.loadClassHistoryFile(btcFile, num,
                                             getEditor().getRelatedEditor());
      refreshContent(editor, btcFile, a_classfile); //messages are displayed
    } catch (CoreException e) {
      MessageDialog.openError(parent, getDescription(),
                              GUIMessages.FAILED_CLASS_FILE_OPERATION);
      return;
    }
  }

  /**
   * The operation to refresh the content of the given editor from the class
   * file is performed. In case of an error an appropriate message
   * is displayed.
   *
   * @param an_editor the editor in which the refresh operation is done
   * @param a_btcfile the .btc file for which the refresh operation is done
   * @param a_classfile the class file corresponding to the .btc file
   * @throws CoreException in case the file system operations cannot be
   *   performed
   */
  private void refreshContent(final BytecodeEditor an_editor,
                              final IFile a_btcfile,
                              final IFile a_classfile)
    throws CoreException {
    final IPath active = a_classfile.getFullPath();
    final BytecodeEditorContributor contributor = getContributor();
    final Shell parent = getEditor().getSite().getShell();
    try {
      final BytecodeDocument doc = an_editor.getDocument();
      an_editor.refreshBytecode(active, doc, null, null);
      final IEditorInput input = new FileEditorInput(a_btcfile);
      //memorise old modification information
      final BytecodeController model = doc.getModel();
      final boolean[] modified = model.getModified();
      contributor.refreshEditor(an_editor, input, null, null);
      an_editor.getDocument().getModel().setModified(modified);
    } catch (ClassNotFoundException e1) {
      //the class corresponding to the Java source code file cannot be found
      MessageDialog.openError(parent, getDescription(),
                              GUIMessages.NO_CLASS_FILE_FOR_SOURCE);
    } catch (UmbraRepresentationException e) {
      wrongRepresentationMessage(parent, getDescription(), e);
    }
    return;
  }

  /**
   * This method asks the user to give the history version number. In case
   * the given value is not a number or is a number outside of the
   * range
   * {@link HistoryOperations#MIN_HISTORY}-{@link HistoryOperations#MAX_HISTORY}
   * the method asks to confirm the default value
   * ({@link HistoryOperations#DEFAULT_HISTORY}). The user can refuse to accept
   * the default and then the procedure repeats.
   *
   * @return the history item number given by the user
   */
  private int getHistoryNum() {
    boolean once_more = true;
    int num = HistoryOperations.DEFAULT_HISTORY;
    while (once_more) {
      final String strnum = JOptionPane.showInputDialog(
        GUIMessages.substitute3(GUIMessages.VERSION_NUMBER_INFORMATION,
                                "" + HistoryOperations.MIN_HISTORY,
                                "" + HistoryOperations.MAX_HISTORY,
                                "" + HistoryOperations.DEFAULT_HISTORY));
      final Shell sh = getEditor().getSite().getShell();
      try {
        num = Integer.parseInt(strnum);
        once_more = false;
      } catch (NumberFormatException ne) {
        num = HistoryOperations.DEFAULT_HISTORY;
        once_more = !MessageDialog.openQuestion(sh, getDescription(),
          GUIMessages.substitute(GUIMessages.NOT_INTEGER_MESSAGE, "" + num));
      }
      if (num > HistoryOperations.MAX_HISTORY ||
          num < HistoryOperations.MIN_HISTORY) {
        num = HistoryOperations.DEFAULT_HISTORY;
        once_more = !MessageDialog.openQuestion(sh, getDescription(),
          GUIMessages.substitute3(GUIMessages.NOT_IN_RANGE_MESSAGE,
                                  "" + HistoryOperations.MIN_HISTORY,
                                  "" + HistoryOperations.MAX_HISTORY,
                                  "" + HistoryOperations.DEFAULT_HISTORY));
      }
    }
    return num;
  }

}
