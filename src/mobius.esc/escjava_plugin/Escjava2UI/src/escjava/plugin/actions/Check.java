package escjava.plugin.actions;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import mobius.util.plugin.JobStatus;
import mobius.util.plugin.Log;
import mobius.util.plugin.Utils;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Shell;

import escjava.plugin.EscjavaChecker;
import escjava.plugin.EscjavaMarker;

/**
 * This class implements the action for checking
 * files using EscJava2.
 * 
 * @author David R. Cok
 */
public class Check extends AEscjavaAction {
  /** if escjava has a working process. */
  private boolean bWorking;
  
  
  /** {@inheritDoc} */
  public final void run(final IAction ac) {
    setDisable();
    bWorking = true;
    final Job job = new Job("ESCJava Check") {
      @Override
      protected IStatus run(final IProgressMonitor monitor) {
        final Shell shell = getWindow().getShell();
        try {
          final List<IAdaptable> list = Utils.getSelectedElements(getSelection(), getWindow());
          if (list.size() == 0) {
            Utils.showMessageInUI(shell, "ESCJava Plugin", "Nothing to check");
          }
          for (IAdaptable adap: list) {
            if (!(adap instanceof IJavaElement)) {
              continue;
            }
            final IJavaElement e = (IJavaElement) adap;
            final boolean checked = checkJavaElement(e);
            if (!checked) {
              final String msg = "Cannot check " + e.getClass();
              Utils.showMessageInUI(shell, "ESCJava Plugin", msg);
            }
          }
        } 
        catch (Exception e) {
          if (getWindow() != null) {
            Utils.showMessageInUI(shell, "ESCJava Plugin - exception",
                                  e.toString());
          }
        }
        bWorking = false;
        setEnabled();
        return JobStatus.getOkStatus();
      }


    };
    job.schedule();
  }
  private void setDisable() {
    getAction().setEnabled(false);
    if (Clear.getInstance() == null) {
      return;
    }
    final IAction clearAction = Clear.getInstance().getAction();
    if (clearAction != null) {
      clearAction.setEnabled(false);
    }
  }

  private void setEnabled(boolean b) {
    if (b) {
      setEnabled();
    }
    else {
      setDisable();
    }
  }
  
  private void setEnabled() {
    if (bWorking) {
      setDisable();
      return;
    }
    getAction().setEnabled(true);
    if (Clear.getInstance() == null) {
      return;
    }
    final IAction clearAction = Clear.getInstance().getAction();
    if (clearAction != null) {
      clearAction.setEnabled(true);
    }
  }
  
  /**
   * TODO
   * @param element
   * @return
   * @throws CoreException 
   */
  public static boolean checkJavaElement(final IJavaElement element) 
    throws CoreException {
    if (element instanceof IJavaProject) {
      checkProject((IJavaProject)element);
    }
    else if (element instanceof IPackageFragment) {
      checkPackage((IPackageFragment)element);
    }
    else if (element instanceof ICompilationUnit) {
      checkCompilationUnit((ICompilationUnit)element);
    }
    else if (element instanceof IType) {
      // should not happen
      checkType((IType)element);
    }
    else {
      return false;
    }
    return true;
  }
  
  /**TODO
   * @param project
   * @throws CoreException 
   */
  private static void checkProject(final IJavaProject project) 
    throws CoreException {
    for (IPackageFragment p: project.getPackageFragments()) {
      checkPackage(p);
    }
  }
  
  /** TODO
   * @param p
   * @throws Exception
   */
  private static void checkPackage(final IPackageFragment p) 
    throws CoreException {
    final List<String> filesToCheck = new LinkedList<String>();
    for (ICompilationUnit cu: p.getCompilationUnits()) {
      filesToCheck.add(cu.getResource().getLocation().toOSString());        
    }
    EscjavaMarker.clearMarkers(p.getResource());
    // FIXME - put package names on command-line?
    try {
      final EscjavaChecker ec = new EscjavaChecker(p.getJavaProject());
      ec.run(filesToCheck);
    }
    catch (Exception e) {
      Log.errorlog("Exception occurred in running ESCJava checks: ", e);
    }    
  }
  
  /**TODO
   * @param p
   * @throws JavaModelException
   * @throws CoreException
   */
  private static void checkCompilationUnit(final ICompilationUnit p) 
    throws CoreException  {
    final IResource resource = p.getUnderlyingResource();
    final List<String> list = new ArrayList<String>(1);
    list.add(resource.getLocation().toOSString());
    final IJavaProject jp = p.getJavaProject();
    EscjavaMarker.clearMarkers(resource);
    try {
      final EscjavaChecker ec = new EscjavaChecker(jp);
      ec.run(list);
          

    } 
    catch (Exception e) {
      Log.errorlog("Exception occurred in running ESCJava checks: ", e);
    }
  }
  
  /**
   * Check the given type.
   * @param t the type to check
   * @deprecated does nothing
   */
  private static void checkType(final IType t) {
    System.err.println("TYPE " + t.getFullyQualifiedName());
    // FIXME
  }
  public void selectionChanged(final IAction ac, final ISelection sel) {
    super.selectionChanged(ac, sel);
    if (sel instanceof IStructuredSelection) {
      final IStructuredSelection ss = (IStructuredSelection) sel;
      setEnabled(ss.getFirstElement() instanceof IJavaElement);
    }
    else {
      setDisable();
    }
    //System.err.println("SEL CHANGED " + selection.getClass());
  }
  // FIXME - want to check only a method as well.

}
