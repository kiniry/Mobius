/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.actions;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;

import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeEditorContributor;
import umbra.editor.ColorModeContainer;
import umbra.editor.parsing.ColorValues;
import umbra.lib.EclipseIdentifiers;
import umbra.lib.GUIMessages;
import umbra.lib.UmbraRepresentationException;

/**
 *  This class defines an action of changing the coloring style. Two
 *  instances of the class are used - one increases the coloring
 *  style mode and the other decreased the mode.
 *
 *  @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 *  @author Aleksy Schubert (alx@mimuw.edu.pl)
 *  @version a-01
 */
public class BytecodeColorAction extends BytecodeEditorAction {

  /**
   * The number which decides on how the colouring mode
   * changes (+1 for increasing, -1 for decreasing).
   */
  private int my_colour_delta;
  //@ invariant my_colour_delta==1 || my_colour_delta == -1;

  /**
   * The current colouring style, see {@link umbra.editor.parsing.ColorValues}.
   */
  private int my_mod;

  /*@ requires change==1 || change == -1;
    @
    @*/

  /**
   * This constructor creates the action to change the
   * clouring mode. It registers the name of the action
   * and stores locally the object which creates all the actions
   * and which contributs the editor GUI elements to the eclipse GUI, and
   * the information on the color change direction (+/-1), and the current
   * colouring mode value.
   *
   * @param a_contr the current manager that initialises actions for
   *    the bytecode plugin
   * @param a_bytecode_contribution the GUI elements contributed to the eclipse
   *   GUI by the byte code editor. This reference should be the same as in the
   *   parameter <code>a_contr</code>.
   * @param a_change +1 for increasing, -1 for decreasing the colouring
   *    mode
   * @param a_mode the initial colouring mode
   */
  public BytecodeColorAction(final BytecodeEditorContributor a_contr,
                final BytecodeContribution a_bytecode_contribution,
                final int a_change,
                final int a_mode) {
    super(EclipseIdentifiers.COLOR_ACTION_NAME, a_contr,
          a_bytecode_contribution);
    this.my_colour_delta = a_change;
    this.my_mod = a_mode;
  }


  /**
   * This method changes global value related to the coloring style
   * and refreshes the editor window.
   */
  public final void run() {
    if (my_mod == ColorValues.MODES_DESC.length - 1) return;
    my_mod = (my_mod + my_colour_delta) % (ColorValues.MODES_DESC.length - 1);
    ColorModeContainer.setMod(my_mod);
    if (getEditor() != null) {
      final Shell sh = getEditor().getSite().getShell();
      try {
        getContributor().refreshEditor(getEditor(), null, null);
      } catch (PartInitException e) {
        MessageDialog.openError(sh, getDescription(),
          GUIMessages.COLOURING_REFRESH_IMPOSSIBLE_MESSAGE);
      } catch (UmbraRepresentationException e) {
        wrongRepresentationMessage(sh, getDescription(), e);
      }
    }
  }

  /**
   * This method sets the bytecode editor for which the
   * action to change the colouring mode will be executed.
   *
   * @param a_part the bytecode editor for which the action will be
   *    executed
   */
  public final void setActiveEditor(final IEditorPart a_part) {
    super.setActiveEditor(a_part);
    my_mod = ColorModeContainer.getMod();
  }
}
