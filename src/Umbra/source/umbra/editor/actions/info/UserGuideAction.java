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
 * The class implements the behaviour in case the User Guide button
 * is pressed.
 *
 * @author Wojtek W�s
 */
public class UserGuideAction implements IEditorActionDelegate {

  /**
   * The method sets the editor associated with the action.
   */
  public void setActiveEditor(final IAction action, final IEditorPart targetEditor) {
  }

  /**
   * The method shows the content of the file with the guiding
   * instructions.
   */
  public final void run(final IAction action) {

    
    final IWorkbenchHelpSystem help = PlatformUI.getWorkbench().getHelpSystem();
    //FIXME open something more specific, note that it is tricky to know the
    // proper ID to open
    // it should open Info/guide.txt
    help.displayHelp();
  }


  /**
   * Currently, does nothing.
   */
  public void selectionChanged(final IAction action, final ISelection selection) {

  }

}
