package ie.ucd.bon.plugin.ui.actions;

import ie.ucd.bon.API;
import ie.ucd.bon.clinterface.BONcOptionsInterface.Print;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.plugin.builder.BONResourceVisitor;
import ie.ucd.bon.plugin.util.PluginUtil;
import ie.ucd.bon.printer.BONPrintMonitor;

import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.ui.PlatformUI;

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
          IRunnableWithProgress irwp = new IRunnableWithProgress() {            
            public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
              Collection<File> files = PluginUtil.getFiles(allResources);
              ParsingTracker tracker = API.parse(files, false, false);
              if (tracker.continueFromParse()) {
                API.print(Print.NEWHTML, false, outputFile, tracker, true, false, new BONProgressMonitor(monitor));
              }
            }
          };
          try {
            PlatformUI.getWorkbench().getProgressService().run(true, true, irwp);
          } catch (InterruptedException ie) {
            System.out.println("Interrupted");
          } catch (InvocationTargetException ite) {
            
          }

        } else {
          //TODO dialog...
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
      monitor.done();
      new ErrorDialog(getTargetPart().getSite().getShell(), "Error generating BON documentation", errorMessage, null, IStatus.ERROR);
    }
  }

}
