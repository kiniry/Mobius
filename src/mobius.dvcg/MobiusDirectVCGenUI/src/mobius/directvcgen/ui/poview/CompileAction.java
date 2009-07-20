package mobius.directvcgen.ui.poview;

import java.io.File;

import mobius.bicolano.BicolanoUtil;
import mobius.directVCGen.clops.DirectVCGenMain;
import mobius.directvcgen.ui.poview.util.RefreshUtils;
import mobius.directvcgen.ui.poview.util.ConsoleUtils.ConsoleOutputWrapper;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.launching.JavaRuntime;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

/**
 * An action triggered by the compilation button.
 * It is supposed to compile the selected file.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CompileAction implements IWorkbenchWindowActionDelegate {
  /** the current selection. */
  private ICompilationUnit fSel;
  
  /** {@inheritDoc} */
  public void dispose() { }

  /** {@inheritDoc} */
  public void init(final IWorkbenchWindow window) { }

  /** {@inheritDoc} */
  public void run(final IAction action) {
    
    if (fSel != null) {
      final ConsoleOutputWrapper wrapper = new ConsoleOutputWrapper();

      wrapper.wrap();
      final String [] args = computeArgs();      
      try {
        DirectVCGenMain.main(args);
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

  /**
   * Compute the arguments of the system call.
   * 
   * @return an array of the arguments for the MobiusDirectVCGen
   */
  private String[] computeArgs() {
    
    try { // computing the arguments
      final IPath path = fSel.getCorrespondingResource().getProject().getLocation();
      
      final String bico = BicolanoUtil.getBicolanoPath();
      String[] classPath = null;
      classPath = JavaRuntime.computeDefaultRuntimeClassPath(fSel.getJavaProject());
      String res = "";
      for (String s: classPath) {
        res += ":" + s;
      }
      final File mobiusPath = new File(path.toString(), "mobius");
      mobiusPath.mkdirs();
      final String[] args = new String[] {
        mobiusPath.getAbsolutePath(), 
        bico, 
        fSel.getTypes()[0].getFullyQualifiedName(),
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

  /** {@inheritDoc} */
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
