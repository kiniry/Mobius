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
  ICompilationUnit sel;
  @Override
  public void dispose() { }

  @Override
  public void init(final IWorkbenchWindow window) { }

  @Override
  public void run(final IAction action) {
    if (sel != null) {

      try {
        final IPath path = sel.getCorrespondingResource().getProject().getLocation();

        final URL url = Activator.getDefault().getBundle().getResource("/lib/bicolano.jar");
        final String bico = FileLocator.toFileURL(url).getPath();
        //final IVMInstall vm = JavaRuntime.getDefaultVMInstall();
        //final IVMRunner runner = vm.getVMRunner(ILaunchManager.RUN_MODE);

        String[] classPath = null;

        classPath = JavaRuntime.computeDefaultRuntimeClassPath(sel.getJavaProject());
        String res = "";
        for (String s: classPath) {
          res += ":" + s;
        }
        System.out.println(res);
        final ConsoleOutputWrapper wrapper = new ConsoleOutputWrapper();
        wrapper.wrap();
        Main.main(new String[]{path.toString(), bico, 
                               sel.getCorrespondingResource().getLocation().toString(),
                               "-classpath", res.substring(1)});
        wrapper.unwrap();
 
        RefreshUtils.refreshResource(sel.getJavaProject().getProject());
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

    }

  }

  @Override
  public void selectionChanged(final IAction action, final ISelection s) {
    if (!s.isEmpty()) {
      if (s instanceof IStructuredSelection) {
        final IStructuredSelection select = (IStructuredSelection) s; 
        final Object o = select.getFirstElement();
        if (o instanceof ICompilationUnit) {
          sel = (ICompilationUnit) o;
        }
      }
    }
  }

}
