package beetlzplugin.popup.actions;

import java.util.Iterator;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

/**
 * Action for remove markers menu item.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class RemoveMarkerAction implements IObjectActionDelegate {
  /** Selected resources. */
  private ISelection my_selection;
  /** Current Eclipse shell. */
  private Shell my_shell;
  /** Current project, or at least one of them. */
  private IProject my_project;

  /**
   * Constructor for Action1.
   */
  public RemoveMarkerAction() {
    super();
  }

  /**
   * @see IObjectActionDelegate#setActivePart(IAction, IWorkbenchPart)
   */
  public void setActivePart(final IAction action, final IWorkbenchPart targetPart) {
    my_shell = targetPart.getSite().getShell();
  }

  /**
   * Here's the actual action performed.
   * @see IActionDelegate#run(IAction)
   */
  public void run(final IAction action) {

    if (!my_selection.isEmpty() && my_selection instanceof IStructuredSelection) {
      final IStructuredSelection sSelection = (IStructuredSelection) my_selection;
      for (final Iterator < ? > iter = sSelection.iterator(); iter.hasNext();) {
        final Object element = iter.next();
        //Is a project selected?
        if (element instanceof IProject) {
          my_project = (IProject) element;
          try {
            my_project.deleteMarkers(BeetlzCheck.JAVA_ERROR_MARKER_ID,
                false, IResource.DEPTH_INFINITE);
            my_project.deleteMarkers(BeetlzCheck.JAVA_WARNING_MARKER_ID,
                false, IResource.DEPTH_INFINITE);
            my_project.deleteMarkers(BeetlzCheck.JML_ERROR_MARKER_ID,
                false, IResource.DEPTH_INFINITE);
            my_project.deleteMarkers(BeetlzCheck.JML_WARNING_MARKER_ID,
                false, IResource.DEPTH_INFINITE);
            my_project.deleteMarkers(BeetlzCheck.NO_LOC_MARKER_ID,
                false, IResource.DEPTH_INFINITE);
          }
          catch (final Exception e){}
        }
        else if (element instanceof IResource) {
          final IResource file = (IResource) element;
          try {
            file.deleteMarkers(BeetlzCheck.JAVA_ERROR_MARKER_ID,
                false, IResource.DEPTH_INFINITE);
            file.deleteMarkers(BeetlzCheck.JAVA_WARNING_MARKER_ID,
                false, IResource.DEPTH_INFINITE);
            file.deleteMarkers(BeetlzCheck.JML_ERROR_MARKER_ID,
                false, IResource.DEPTH_INFINITE);
            file.deleteMarkers(BeetlzCheck.JML_WARNING_MARKER_ID,
                false, IResource.DEPTH_INFINITE);
            file.deleteMarkers(BeetlzCheck.NO_LOC_MARKER_ID, false, IResource.DEPTH_INFINITE);
          }
          catch (final Exception e){}
          if (my_project == null) {
            my_project = ((IResource) element).getProject();
          }
        }
      }
    }




  }

  /**
   * @see IActionDelegate#selectionChanged(IAction, ISelection)
   */
  public void selectionChanged(final IAction action, final ISelection selection) {
    my_selection = selection;
  }

}
