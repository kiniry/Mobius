/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.actions;

import javax.swing.JOptionPane;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeEditor;
import umbra.editor.BytecodeEditorContributor;

/**
 * This class defines action of restoring bytecode from
 * history. Current verion is replaced with one of these
 * kept in history as a file with bt1, bt2, etc. extensions.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeRestoreAction extends BytecodeEditorAction {


  /**
   * This constructor creates the action to restore a file stored in the history
   * of the bytecode editor. It registers the name of the action with the text
   * "Restore" and stores locally the object which creates all the actions
   * and which contributs the editor GUI elements to the eclipse GUI.
   *
   * @param a_contributor the manager that initialises all the actions within
   * the bytecode plugin
   * @param a_btcd_contribution the GUI elements contributed to the eclipse
   * GUI by the bytecode editor. This reference should be the same as in the
   * parameter <code>a_contributor</code>.   */
  public BytecodeRestoreAction(final BytecodeEditorContributor a_contributor,
                 final BytecodeContribution a_btcd_contribution) {
    super("Restore", a_contributor, a_btcd_contribution);
  }

  /**
   * An input dialog to insert number of version is shown.
   * Then the binary source file is replaced with the
   * appropriate historical version and new input is
   * generated and put into the editor window.
   */
  public final void run() {
    final int num = getHistoryNum();
    final String ext = UmbraHelper.BYTECODE_HISTORY_EXTENSION + num;
    final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    final BytecodeEditor editor = (BytecodeEditor)getEditor();
    final IFile btcFile = ((FileEditorInput)editor.getEditorInput()).getFile();
    IFile afile;
    try {
      afile = UmbraHelper.getClassFileFileFor(btcFile,
                                             editor.getRelatedEditor(),
                                             UmbraHelper.BYTECODE_EXTENSION);
    } catch (JavaModelException e2) {
      e2.printStackTrace();
      afile = replaceBytecodeWithClass(btcFile);
    }
    final IPath active = afile.getFullPath();
    final String history_fname = active.toOSString().replaceFirst(
                   UmbraHelper.BYTECODE_EXTENSION,
                   ext);
    final IFile history_file = root.getFile(new Path(history_fname));
    if (!history_file.exists()) {
      final Shell shell = editor.getSite().getShell();
      MessageDialog.openInformation(shell, "Restore bytecode",
          "The file " + history_fname + " does not exist");
      return;
    }
    try {
      btcFile.delete(true, null);
      history_file.copy(active, true, null);
    } catch (CoreException e) {
      e.printStackTrace();
    }
    final String clnameTo = afile.getFullPath().toPortableString();
    final String lastSegment = afile.getFullPath().lastSegment();
    final String clnameFrom = active.removeLastSegments(1).append("_" +
                                    num + "_" + lastSegment).toPortableString();
    final IFile classFrom = root.getFile(new Path(clnameFrom));
    final IPath clpathTo = new Path(clnameTo);
    final IFile classTo = root.getFile(clpathTo);
    try {
      classTo.delete(true, null);
      classFrom.copy(clpathTo, true, null);
    } catch (CoreException e) {
      e.printStackTrace();
    }
    final BytecodeEditorContributor contributor = getContributor();
    try {
      final BytecodeContribution bytecodeContribution = getContribution();
      ((BytecodeEditor)editor).refreshBytecode(active, null, null);
      final IEditorInput input = new FileEditorInput(btcFile);
      final boolean[] modified = bytecodeContribution.getModified();
      bytecodeContribution.setModTable(modified);
      contributor.refreshEditor(editor, input);
    } catch (ClassNotFoundException e1) {
      e1.printStackTrace();
    } catch (CoreException e1) {
      e1.printStackTrace();
    }
    contributor.synchrEnable();
  }

  /**
   * TODO.
   * @param a_btc_file TODO
   * @return TODO.
   */
  private IFile replaceBytecodeWithClass(final IFile a_btc_file) {
    final IPath aPath = a_btc_file.getFullPath();
    final String lastSegment = UmbraHelper.replaceLast(aPath.lastSegment(),
                                        UmbraHelper.BYTECODE_EXTENSION,
                                        UmbraHelper.CLASS_EXTENSION);
    final String fname = aPath.removeLastSegments(1).append(lastSegment).
                                                     toPortableString();
    final IWorkspace workspace = ResourcesPlugin.getWorkspace();
    return workspace.getRoot().getFile(Path.fromPortableString(fname));
  }

  /**
   * This method asks the user to give the history version number. In case
   * the given value is not a number or is a number outside of the
   * range {@ref UmbraHelper#MIN_HISTORY}-{@ref UmbraHelper#MAX_HISTORY}
   * the method asks to confirm the default value
   * ({@ref UmbraHelper#DEFAULT_HISTORY}). The user can refuse to accept the
   * default and then the procedure repeats.
   *
   * @return the history item number given by the user
   */
  private int getHistoryNum() {
    boolean once_more = true;
    int num = UmbraHelper.DEFAULT_HISTORY;
    while (once_more) {
      final String strnum = JOptionPane.showInputDialog("Input version " +
                               "number (" + UmbraHelper.MIN_HISTORY + " to " +
                                            UmbraHelper.MAX_HISTORY + "):",
                               "" + UmbraHelper.DEFAULT_HISTORY);
      try {
        num = Integer.parseInt(strnum);
      } catch (NumberFormatException ne) {
        num = UmbraHelper.DEFAULT_HISTORY;
        once_more = !MessageDialog.openQuestion(getEditor().getSite().
                                                            getShell(),
                                "Bytecode", "It's not an integer. " +
                                            "Should we use " +
                                            num + " instead");
      }
      if (num > UmbraHelper.MAX_HISTORY || num < UmbraHelper.MIN_HISTORY) {
        num = UmbraHelper.DEFAULT_HISTORY;
        once_more = !MessageDialog.openQuestion(getEditor().getSite().
                                                            getShell(),
                                              "Bytecode",
                                              "It's not in the range " +
                                              "(" + UmbraHelper.MIN_HISTORY +
                                              " to " +
                                              UmbraHelper.MAX_HISTORY + ")." +
                                              "Should we use " +
                                              UmbraHelper.DEFAULT_HISTORY +
                                              "?");
      }
    }
    return num;
  }

}
