package ie.ucd.bon.plugin.ui.actions;

import ie.ucd.bon.API;
import ie.ucd.bon.clinterface.BONcOptionsInterface.Print;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.plugin.BONPlugin;
import ie.ucd.bon.plugin.builder.BONResourceVisitor;
import ie.ucd.bon.plugin.util.PluginUtil;
import ie.ucd.bon.printer.BONPrintMonitor;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.IAction;
import org.eclipse.swt.widgets.DirectoryDialog;

public class GenerateBONDocumentationAction extends AllSelectedResourcesAction {

  @Override
  protected void run(IAction action, List<IResource> resources) {
    final List<IResource> allResources = new ArrayList<IResource>(); 
    for (IResource resource : resources) {
      allResources.addAll(BONResourceVisitor.getBONResources(resource));
    }

    //TODO suggested folder for output.

    String outputFileString = doOutputFileDialog();
    if (outputFileString != null) {
      if (outputFileString != null) {
        final File outputFile = new File(outputFileString);
        if (outputFile.isDirectory()) {
          final Collection<File> files = PluginUtil.getFiles(allResources);
          Job job = new Job("Generating BON Documentation") {
            @Override
            protected IStatus run(IProgressMonitor monitor) {
              final BONProgressMonitor bMonitor = new BONProgressMonitor(monitor);
              ParsingTracker tracker = API.parse(files, false, false);
              if (tracker.continueFromParse()) {
                API.print(Print.NEWHTML, false, outputFile, tracker, true, false, bMonitor);
              }

              if (bMonitor.errorMessage != null) {
                return new Status(IStatus.ERROR, BONPlugin.PLUGIN_ID, bMonitor.errorMessage);
              } else if (monitor.isCanceled()) {
                return Status.CANCEL_STATUS;
              } else   {
                return Status.OK_STATUS;
              }
            }
          };
          job.schedule();

        } else {
          //TODO dialog...
          System.out.println("Not a directory");
        }
      } else {
        System.out.println("No file selected");
      }
    }
  }

  private String doOutputFileDialog() {
    //ChooseOutputFileDialog dialog = new ChooseOutputFileDialog(getTargetPart().getSite().getShell());
    DirectoryDialog dialog = new DirectoryDialog(getTargetPart().getSite().getShell());
    dialog.setText("Select output directory");
    return dialog.open();
  }

  private final class BONProgressMonitor implements BONPrintMonitor {

    private final IProgressMonitor monitor;
    String errorMessage;

    public BONProgressMonitor(IProgressMonitor monitor) {
      this.monitor = monitor;
    }

    public void begin(String info, int totalTasks) {
      monitor.beginTask(info, totalTasks);
    }

    public boolean isCancelled() {
      return monitor.isCanceled();
    }

    public void progress(int completed) {
      monitor.worked(completed);
    }

    public void setInfo(String info) {
      monitor.setTaskName(info);
    }

    public void complete() {
      monitor.done();
    }

    public void finishWithErrorMessage(String errorMessage) {
      this.errorMessage = errorMessage;
      System.out.println("Finished with error: " + errorMessage);
      monitor.done();
    }
  }

}
