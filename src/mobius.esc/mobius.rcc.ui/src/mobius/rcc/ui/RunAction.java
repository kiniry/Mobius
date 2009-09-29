package mobius.rcc.ui;

import mobius.util.plugin.ConsoleUtils.ConsoleOutputWrapper;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

public class RunAction implements IWorkbenchWindowActionDelegate {
  /** the current selection. */
  private ICompilationUnit fSel;
  
  public void dispose() {
    // TODO Auto-generated method stub

  }

  public void init(IWorkbenchWindow window) {
    // TODO Auto-generated method stub

  }

  public void run(IAction action) {
    if (fSel != null) {
      final ConsoleOutputWrapper wrapper = new ConsoleOutputWrapper();

      wrapper.wrap();
      final String [] args = computeArgs();      
      try {
        Main.main(args);
      }  
      catch (IllegalArgumentException e) {
        e.printStackTrace();
      }
      catch (Throwable e) {
        e.printStackTrace();
      }
      finally {
        wrapper.unwrap();
        //RefreshUtils.refreshResource(fSel.getJavaProject().getProject()); 
      }

    }
  }

  private String[] computeArgs() {
    // TODO Auto-generated method stub
    return null;
  }

  public void selectionChanged(IAction action, ISelection s) {
    if (!s.isEmpty()) {
      if (s instanceof IStructuredSelection) {
        final IStructuredSelection select = (IStructuredSelection) s; 
        final Object o = select.getFirstElement();
        if (o instanceof ICompilationUnit) {
          fSel = (ICompilationUnit) o;
        }
      }
    }
  }

}
