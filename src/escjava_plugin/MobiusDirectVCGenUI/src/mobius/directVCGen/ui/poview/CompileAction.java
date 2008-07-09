package mobius.directVCGen.ui.poview;

import java.io.File;
import java.io.IOException;
import java.net.URL;

import mobius.directVCGen.Main;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.core.Launch;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.launching.IVMInstall;
import org.eclipse.jdt.launching.IVMRunner;
import org.eclipse.jdt.launching.JavaRuntime;
import org.eclipse.jdt.launching.VMRunnerConfiguration;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

public class CompileAction implements IWorkbenchWindowActionDelegate {
  ICompilationUnit sel;
  @Override
  public void dispose() {
    // TODO Auto-generated method stub

  }

  @Override
  public void init(IWorkbenchWindow window) {
    // TODO Auto-generated method stub

  }

  @Override
  public void run(final IAction action) {
    System.out.println("Action time");
    if (sel != null) {
      System.out.println("and vision!");

      try {
        final IPath path = sel.getCorrespondingResource().getProject().getLocation();

        final URL url = Activator.getDefault().getBundle().getResource("/lib/bicolano.jar");
        final String bico = FileLocator.toFileURL(url).getPath();
        final IVMInstall vm = JavaRuntime.getDefaultVMInstall();
        final IVMRunner runner = vm.getVMRunner(ILaunchManager.RUN_MODE);

        String[] classPath = null;

        classPath = JavaRuntime.computeDefaultRuntimeClassPath(sel.getJavaProject());
        String res = "";
        for (String s: classPath) {
          res += ":" + s;
        }
        System.out.println(res);
        
        Main.main(new String[]{path.toString(), bico, 
                               sel.getCorrespondingResource().getLocation().toString(),
                               "-classpath", res.substring(1)});

      }
      catch (IOException e) {
        e.printStackTrace();
      }
      catch (JavaModelException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } 
      catch (CoreException e) {
        // TODO Auto-generated catch block
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
