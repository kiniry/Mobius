/*
 * Created on 2005-09-06
 */
package umbra.editor.actions.info;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.help.IWorkbenchHelpSystem;

/**
 * TODO
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class InstalInfoAction implements IEditorActionDelegate {

  /**
   * TODO
   */
  private IEditorPart editor;

  /**
   * TODO
   */
  public final void setActiveEditor(final IAction action, final IEditorPart targetEditor) {
    editor = targetEditor;
  }

  /**
   * TODO
   */
  public final void run(final IAction an_action) {

    final IWorkbenchHelpSystem help = PlatformUI.getWorkbench().getHelpSystem();
    //FIXME open something more specific, note that it is tricky to know the
    // proper ID to open
    // it should open Info/info.txt
    help.displayHelp();
  }

  /**
   * TODO
   */
  public void selectionChanged(final IAction action, 
                               final ISelection selection) {
  }
}
