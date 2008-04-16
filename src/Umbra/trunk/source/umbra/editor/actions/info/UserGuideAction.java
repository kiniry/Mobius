/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.actions.info;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.help.IWorkbenchHelpSystem;

/**
 * The class implements the behaviour in case the User Guide button
 * in the byte code editor is pressed.
 *
 * @author Wojciech Wąs  (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class UserGuideAction implements IEditorActionDelegate {

  /**
   * The method sets the editor associated with the action.
   *
   * @param an_action ignored
   * @param a_target_editor ignored
   */
  public void setActiveEditor(final IAction an_action,
                              final IEditorPart a_target_editor) {
  }

  /**
   * The method shows the content of the user guide instructions.
   * Currently, it only pops up the general help browser.
   *
   * FIXME the method should open something more specific, note that it is
   * tricky to know the proper ID to open it should open something like
   * Info/guide.txt
   * https://mobius.ucd.ie/ticket/556
   *
   * @param an_action action that triggered the showing of the instruction
   */
  public final void run(final IAction an_action) {

    final IWorkbenchHelpSystem help = PlatformUI.getWorkbench().getHelpSystem();
    help.displayHelpResource("/mobius.umbra/help/user_guide.html");
  }


  /**
   * The method reacts when the selected area changes in the byte code
   * editor. Currently, it does nothing.
   *
   * @param an_action the action which triggered the selection change
   * @param a_selection the new selection.
   */
  public void selectionChanged(final IAction an_action,
                               final ISelection a_selection) {
  }

}
