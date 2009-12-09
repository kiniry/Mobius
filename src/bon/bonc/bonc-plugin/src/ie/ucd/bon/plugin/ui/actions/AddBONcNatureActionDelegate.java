package ie.ucd.bon.plugin.ui.actions;

import ie.ucd.bon.plugin.BONPlugin;
import ie.ucd.bon.util.StringUtil;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;

public class AddBONcNatureActionDelegate extends AllSelectedProjectsAction {

  @Override
  protected void run(IAction action, List<IProject> projects) {
    int count = 0;
    List<String> names = new ArrayList<String>();

    for (IProject project : projects) {
      if (!project.isOpen()) {
        continue;
      }

      IProjectDescription description;
      try {
        description = project.getDescription();
      } catch (CoreException e) {
        //e.printStackTrace();
        continue;
      }

      List<String> newIds = new ArrayList<String>();
      newIds.addAll(Arrays.asList(description.getNatureIds()));

      if (!newIds.contains(BONPlugin.NATURE_ID)) {
        newIds.add(BONPlugin.NATURE_ID);
        description.setNatureIds(newIds.toArray(new String[newIds.size()]));

        try {
          project.setDescription(description, null);
          names.add(project.getDescription().getName());
          count++;
        } catch (CoreException e) {
          //e.printStackTrace();
        }

      }
    }

    if (count == 1) {
      MessageDialog.openInformation(getTargetPart().getSite().getShell(), "Added BONc nature", "BONc nature added to project " + StringUtil.appendWithSeparator(names, ", "));
    } else if (count > 1) {
      MessageDialog.openInformation(getTargetPart().getSite().getShell(), "Added BONc nature", "BONc nature added to projects: " + StringUtil.appendWithSeparator(names, ", "));
    }
  }



}
