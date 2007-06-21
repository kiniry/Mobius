/**
 * 
 */
package umbra.editor.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.ui.IEditorPart;

import umbra.editor.BytecodeContribution;
import umbra.editor.BytecodeEditorContributor;

/**
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class BytecodeEditorAction extends Action {

  /**
   * The current bytecode editor for which the action takes place.
   */
  private IEditorPart my_editor;

  /**
   * The manager that initialises all the actions within the
   * bytecode plugin.
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
   * This constructor creates the generic part of a bytecode editor action.
   * It registers the action under the title givem by <code>a_name</code>
   * parameter and stores locally the object which creates all the actions
   * and which contributes the editor GUI elements to the eclipse GUI.
   *
   * @param a_name a name of the action to register
   * @param a_contributor the manager that initialises all the actions within
   * the bytecode plugin
   * @param a_bytecode_contribution the GUI elements contributed to the eclipse
   * GUI by the bytecode editor. This reference should be the same as in the
   * parameter <code>a_contributor</code>.
   */
  public BytecodeEditorAction(final String a_name,
                          final BytecodeEditorContributor a_contributor,
                          final BytecodeContribution a_bytecode_contribution) {
    super(a_name);
    my_contributor = a_contributor;
    my_btcodeCntrbtn = a_bytecode_contribution;
  }


  /**
   * The method sets the editor for which the operation to combine
   * the modifications in the source code and in the byte code will
   * be performed.
   *
   * @param a_part the editor to combine modifications
   */
  public void setActiveEditor(final IEditorPart a_part) {
    my_editor = a_part;
  }

  /**
   * @return the bytecode editor currently associated with the action
   */
  public final IEditorPart getEditor() {
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
}
