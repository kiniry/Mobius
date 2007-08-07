/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.java.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;

/**
 * The action is used to convert Java Bytecode into BoogiePL.
 *
 * @author Samuel Willimann  (wsamuel@student.ethz.ch)
 * @version a-01
 *
 */
public class VerifyAction implements IEditorActionDelegate {

  /**
   * The method sets the internal Java source code editor attribute.
   * Currently it does nothing.
   *
   * TODO probably the content should be filled in.
   *
   * @param an_action the action which triggered the change of the editor
   * @param a_java_editor the new Java source code editor to be associated with
   * the action
   */
  public void setActiveEditor(final IAction an_action,
                              final IEditorPart a_java_editor) {
  }

  /**
   * This method handles the action of the verification action.
   * Currently it does nothing.
   *
   * TODO probably the content should be filled in.
   *
   * @param an_action the action that triggered the operation
   */
  public final void run(final IAction an_action) {

    // TODO convert Bytecode to BoogiePL


    // TODO Run Boogie on the generated BoogiePL program

    return;
  }

  /**
   * Currently, does nothing.
   *
   * TODO probably the content should be filled in.
   *
   * @param an_action see {@ref IActionDelegate#selectionChanged(IAction,
   *                       ISelection)}
   * @param a_selection see {@ref IActionDelegate#selectionChanged(IAction,
   *                       ISelection)}
   */
  public void selectionChanged(final IAction an_action,
                               final ISelection a_selection) {
    //Currently, does nothing.
  }
}
