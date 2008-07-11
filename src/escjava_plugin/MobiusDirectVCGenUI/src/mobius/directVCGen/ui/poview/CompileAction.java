package mobius.directVCGen.ui.poview;

import java.io.IOException;
import java.net.URL;

import mobius.directVCGen.Main;
import mobius.directVCGen.ui.poview.util.RefreshUtils;
import mobius.directVCGen.ui.poview.util.ConsoleUtils.ConsoleOutputWrapper;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.launching.JavaRuntime;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

public class CompileAction implements IWorkbenchWindowActionDelegate {
  /** the current selection. */
  private ICompilationUnit fSel;
  
  /** {@inheritDoc} */
  @Override
  public void dispose() { }

  /** {@inheritDoc} */
  @Override
  public void init(final IWorkbenchWindow window) { }

  /** {@inheritDoc} */
  @Override
  public void run(final IAction action) {
    
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
        RefreshUtils.refreshResource(fSel.getJavaProject().getProject()); 
      }

    }

  }

  private String[] computeArgs() {
    String[] args = new String[0];
    try { // computing the arguments
      final IPath path = fSel.getCorrespondingResource().getProject().getLocation();

      final URL url = Activator.getDefault().getBundle().getResource("/lib/bicolano.jar");
      final String bico = FileLocator.toFileURL(url).getPath();
 
      String[] classPath = null;

      classPath = JavaRuntime.computeDefaultRuntimeClassPath(fSel.getJavaProject());
      String res = "";
      for (String s: classPath) {
        res += ":" + s;
      }
      args = new String[] {
        path.toString(), bico, 
        fSel.getTypes()[0].getFullyQualifiedName(),
        "-cp", res.substring(1), 
        "-SourcePath", 
        fSel.getResource().getParent().getLocation().toString()
      };
    }
    catch (IOException e) {
      e.printStackTrace();
    }
    catch (JavaModelException e) {
      e.printStackTrace();
    } 
    catch (CoreException e) {
      e.printStackTrace();
    }
    return args;
  }

  /** {@inheritDoc} */
  @Override
  public void selectionChanged(final IAction action, final ISelection s) {
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
