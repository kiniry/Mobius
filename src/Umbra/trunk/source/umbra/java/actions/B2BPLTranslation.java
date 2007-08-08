package umbra.java.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;

/**
 * Calls the Java Bytecode to BoogiePL translator (B2BPL).
 * @author Samuel Willimann
 *
 */
public class B2BPLTranslation implements IEditorActionDelegate {

  /**
   * Changes the active editor.
   * @param action IAction
   * @param targetEditor IEditorPart
   */
  public final void setActiveEditor(final IAction action,
                                    final IEditorPart targetEditor) {
    // TODO Auto-generated method stub
    System.out.println("setActiveEditor");
  }

  /**
   * Runs the translatior.
   * @param action IAction
   */
  public final void run(final IAction action) {
    // TODO Auto-generated method stub
    System.out.println("run");
  }

  /**
   * Selection changes.
   * @param action IAction
   * @param selection ISelection
   */
  public final void selectionChanged(final IAction action,
                                     final ISelection selection) {
    // TODO Auto-generated method stub
    System.out.println("selectionChanged");
  }

}
