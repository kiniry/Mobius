/**
 *
 */
package umbra.editor.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;

import umbra.editor.BytecodeEditorContributor;
import umbra.editor.Composition;
import umbra.editor.IColorValues;

/**
 *  This class defines an action of changing the coloring style. Two
 *  instances of the class are used - one increases the coloring
 *  style mode and the other decreased the mode.
 *
 *  @author Wojtek Wąs (ww209224@students.mimuw.edu.pl)
 *  @version a-01
 */
public class BytecodeEditorAction extends Action {
  /**
   * The current bytecode editor for which the action takes place.
   */
  private IEditorPart my_active_editor;

  /**
   * The number which decides on how the colouring mode
   * changes (+1 for increasing, -1 for decreasing).
   */
  private int my_colour_delta;
  //@ invariant my_colour_delta==1 || my_colour_delta == -1;

  /**
   * The current colouring style, see {@link IColorValues}.
   */
  private int my_mod;

  /**
   * The manager that initialises all the actions within the
   * bytecode plugin.
   */
  private BytecodeEditorContributor my_contributor;

  /*@ requires change==1 || change == -1;
    @
    @*/
  /**
   * This constructor creates the action to change the
   * clouring mode.
   *
   * @param a_contr the current manager that initialises actions for
   *                the bytecode plugin
   * @param a_change +1 for increasing, -1 for decreasing the colouring
   *    mode
   * @param a_mode the initial colouring mode
   */
  public BytecodeEditorAction(final BytecodeEditorContributor a_contr,
                final int a_change,
                final int a_mode) {
    super("Change color");
    this.my_colour_delta = a_change;
    this.my_mod = a_mode;
    this.my_contributor = a_contr;
  }


  /**
   * This method changes global value related to the coloring style
   * and refreshes the editor window.
   */
  public final void run() {
    if (my_mod == IColorValues.MODELS.length - 1) return;
    my_mod = (my_mod + my_colour_delta) % (IColorValues.MODELS.length - 1);
    Composition.setMod(my_mod);
    if (my_active_editor != null) {
      try {
        my_contributor.refreshEditor(my_active_editor);
      } catch (PartInitException e) {
        MessageDialog.openWarning(my_active_editor.getSite().getShell(),
            "Bytecode", "Cannot open a new editor after closing " +
                  "the old one");
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
  public final void setMy_active_editor(final IEditorPart a_part) {
    my_active_editor = a_part;
    my_mod = Composition.getMod();
  }
}
