package escjava.plugin.actions;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import mobius.util.plugin.ImagesUtils;
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
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.IType;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchWindowPulldownDelegate;

import escjava.plugin.EscjavaMarker;
import escjava.plugin.EscjavaPlugin;
import escjava.plugin.checkers.Checker;
import escjava.plugin.checkers.Cvc3Checker;
import escjava.plugin.checkers.Z3Checker;

/**
 * This class implements the action for checking
 * files using EscJava2.
 * 
 * @author David R. Cok
 */
public class Check extends AEscjavaAction implements IWorkbenchWindowPulldownDelegate {
  private static Check inst = new Check();
  /** if escjava has a working process. */
  private boolean bWorking;
  
  protected enum Prover {
    /** simplify prover the default one. */
    simplify("Simplify", "icons/esc.png"), 
    /** cvc3 prover. */
    cvc3("Cvc3", "icons/cvc3.png"),  
    /** z3 prover the default one. */
    z3("z3", "icons/z3.png");
    
    /** the proper name of the prover. */
    private final String name;
    /** the path to its icon. */
    private final String iconPath;
    /** the descriptor for the image of the prover. */
    private ImageDescriptor img;
    
    private Prover(final String nam, final String icnPath) {
      name = nam;
      iconPath = icnPath;
    }
    
    /** {@inheritDoc} */
    public String toString() {
      return name;
    }
    /** @return the image descriptor for the checker button */
    public ImageDescriptor getImageDescriptor() {
      if (img == null) {
        img = ImagesUtils.createImageDescriptor(EscjavaPlugin.PLUGIN_ID, iconPath);
      }
      return img;
    }
    
    /** 
     * @param p the project on which to apply the checker.
     * @return the right escjava check corresponding to the given prover. 
     */
    public Checker getChecker(final IJavaProject p) {
      Checker res;
      switch(this) {
        case cvc3:
          res = new Cvc3Checker(p);
          break;
        case z3:
          res = new Z3Checker(p);
          break;
        case simplify:
        default:
          res = new Checker(p);
          break;
      }
      return res;
    }
  }
  
  /** the current selected prover. default is simplify. */
  private Prover prover = Prover.simplify;
  
  /** {@inheritDoc} */
  public final void run(final IAction ac) {
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
    
    bWorking = true;
    setDisable();
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

  protected void setEnabled(boolean b) {
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
  public boolean checkJavaElement(final IJavaElement element) 
    throws CoreException {
    if (element instanceof IJavaProject) {
      checkProject((IJavaProject)element);
    }
    else if (element instanceof IPackageFragment) {
      checkPackage((IPackageFragment)element);
    }
    else if (element instanceof IPackageFragmentRoot) {
      checkPackage((IPackageFragmentRoot)element);
    }
    
    else if (element instanceof ICompilationUnit) {
      checkCompilationUnit((ICompilationUnit)element);
    }
    else if (element instanceof IType) {
      // should not happen
      checkType((IType)element);
      throw new UnsupportedOperationException();
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
  private void checkProject(final IJavaProject project) 
    throws CoreException {
    for (IPackageFragment p: project.getPackageFragments()) {
      checkPackage(p);
    }
  }
  /** TODO
   * @param p
   * @throws Exception
   */
  private void checkPackage(final IPackageFragmentRoot p) 
    throws CoreException {
    for (IJavaElement elem: p.getChildren()) {
      checkJavaElement(elem);
    }
  }
  /** TODO
   * @param p
   * @throws Exception
   */
  private void checkPackage(final IPackageFragment p) 
    throws CoreException {
    final List<String> filesToCheck = new LinkedList<String>();
    for (ICompilationUnit cu: p.getCompilationUnits()) {
      filesToCheck.add(cu.getResource().getLocation().toOSString());        
    }
    
    EscjavaMarker.clearMarkers(p.getResource());
    // FIXME - put package names on command-line?
    try {
      final Checker ec = prover.getChecker(p.getJavaProject());
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
  private void checkCompilationUnit(final ICompilationUnit p) 
    throws CoreException  {
    final IResource resource = p.getUnderlyingResource();
    final List<String> list = new ArrayList<String>(1);
    list.add(resource.getLocation().toOSString());
    final IJavaProject jp = p.getJavaProject();
    EscjavaMarker.clearMarkers(resource);
    try {
      final Checker ec = prover.getChecker(jp);
      ec.run(list);
          

    } 
    catch (Exception e) {
      Log.errorlog("Exception occurred in running " + EscjavaPlugin.ESC_TOOL_NAME + 
                   " checks: ", e);
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
  
  

  
  public static Check getInstance() {
    return inst;
  }
  
  /** {@inheritDoc} */
  public Menu getMenu(final Control parent) {
    final Menu m = new Menu(parent);
    for (final Prover p: Prover.values()) {
      if (p.equals(Prover.cvc3) && 
          !System.getProperty("os.name").startsWith("Linux")) {
        continue;
      }
      final MenuItem item = new MenuItem(m, SWT.PUSH);
      item.setText("Check with " + p);
      item.setImage(p.getImageDescriptor().createImage());
      item.addSelectionListener(new SelectionListener () {
        public void widgetDefaultSelected(final SelectionEvent e) { }
        public void widgetSelected(final SelectionEvent e) {
          prover = p;
          updateUI();
        }
      });
    }
    return m;
  }
  
  /** Updates the button with the currently selected prover. */
  public void updateUI() {
    final IAction action = Check.this.getAction();
    action.setImageDescriptor(prover.getImageDescriptor());
    action.setText(EscjavaPlugin.ESC_TOOL_NAME + ": Check with " + prover);
    action.setToolTipText("Runs " + EscjavaPlugin.ESC_TOOL_NAME + 
                          " static checks using " + prover);
  }
  
  protected void setProver(final Prover p) {
    prover = p;
  }
}
