package mobius.rcc.ui;

import mobius.util.plugin.JobStatus;
import mobius.util.plugin.ConsoleUtils.ConsoleOutputWrapper;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.launching.JavaRuntime;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

import rcc.Main;

public class RunAction implements IWorkbenchWindowActionDelegate {
  /** the current selection. */
  private ICompilationUnit fSel;
  
  private class RccJob extends Job {
    public RccJob() {
      super("Rcc");
    }

    @Override
    protected IStatus run(IProgressMonitor monitor) {
      final ConsoleOutputWrapper wrapper = new ConsoleOutputWrapper();
      wrapper.wrap();
      System.out.println("Wrapping the standard output.");
      final String [] args = computeArgs();      
      try {
        System.out.print("Calling RCC with the arguments: ");
        for (String a: args) {
          System.out.print(a + " ");
        }
        System.out.println();
        Main.main(args);
      }  
      catch (IllegalArgumentException e) {
        e.printStackTrace();
      }
      catch (Throwable e) {
        e.printStackTrace();
      }
      finally {
        System.out.println("Unwrapping the standard output.");
        wrapper.unwrap();
        //RefreshUtils.refreshResource(fSel.getJavaProject().getProject()); 
      }
      
      return JobStatus.getOkStatus();
    }
  }
  
  /** {@inheritDoc} */
  public void dispose() { }

  /** {@inheritDoc} */
  public void init(IWorkbenchWindow window) { }

  public void run(IAction action) {
    if (fSel != null) {
      Job job = new RccJob();
      job.schedule();
    }
  }

  private String[] computeArgs() {
    try { // computing the arguments      
      String[] classPath = null;
      classPath = JavaRuntime.computeDefaultRuntimeClassPath(fSel.getJavaProject());
      String res = "";
      for (String s: classPath) {
        res += ":" + s;
      }
      final String[] args = new String[] {
        fSel.getResource().getLocation().toString(),
        "-cp", res.substring(1), 
        "-SourcePath", 
        fSel.getResource().getParent().getLocation().toString()
      };
      //System.out.println(res);
      return args;
    } 
    catch (JavaModelException e) {
      e.printStackTrace();
    } 
    catch (CoreException e) {
      e.printStackTrace();
    }
    return new String[0];
  }
  
  
  public void selectionChanged(IAction action, ISelection s) {
    if (!s.isEmpty()) {
      if (s instanceof IStructuredSelection) {
        final IStructuredSelection select = (IStructuredSelection) s; 
        final Object o = select.getFirstElement();
        if (o instanceof ICompilationUnit) {
          action.setEnabled(true);
          fSel = (ICompilationUnit) o;
        }
        else {
          action.setEnabled(false);
        }
      }
    }
  }
}
