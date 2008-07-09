package mobius.directVCGen.ui.poview;

import mobius.directVCGen.ui.poview.tree.AWorkspaceElement;
import mobius.directVCGen.ui.poview.tree.IShowable;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.ToolItem;
import org.eclipse.ui.IPageListener;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;


/**
 * This class represemts the proof obligation viewer.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ProjectProofs extends ViewPart 
  implements IDoubleClickListener, ISelectionChangedListener, SelectionListener, IPageListener {
  /** the current selection. */
  private AWorkspaceElement fSel;
  /** the tree showing all the proofs. */
  private TreeViewer fViewer;
  /** the button that triggers the evaluate action. */
  private ToolItem fBtnEvaluate;
  

  
  /**
   * Create the proof viewer with the tree view.
   * @param parent the parent where to create the viewer
   */
  private void createViewer(final Composite parent) {
    final GridData gd = new GridData();
    gd.horizontalAlignment = GridData.FILL;
    gd.grabExcessHorizontalSpace = true;
    gd.verticalAlignment = GridData.FILL;
    gd.grabExcessVerticalSpace = true;
    fViewer = new TreeViewer(parent, SWT.MULTI | 
                             SWT.H_SCROLL | SWT.V_SCROLL);
    fViewer.getControl().setLayoutData(gd);
    fViewer.setUseHashlookup(true);
    fViewer.setContentProvider(new POsContentProvider(fViewer));
    fViewer.setLabelProvider(new POsLabelProvider());
//    fViewer.setInput(Utils.getProjects());
    fViewer.addDoubleClickListener(this);
    fViewer.addSelectionChangedListener(this);

  }

  private class MySelListener implements ISelectionListener {
    IProject proj;
    @Override
    public void selectionChanged(final IWorkbenchPart part, final ISelection selection) {
      if (selection instanceof IStructuredSelection) {
        final IStructuredSelection sel = (IStructuredSelection) selection;
        //final Set<IProject> set = new HashSet<IProject>();
        if (sel.size() == 1) {
          final Object o = sel.getFirstElement();
          IProject newProj = null;
          if (o instanceof IResource) {
            final IResource res = (IResource) o;
            newProj = res.getProject();
          }
          if (o instanceof IProject) {
            newProj = (IProject) o;
          }
          if (o instanceof IJavaElement) {
            final IJavaElement elem = (IJavaElement) o;
            newProj = elem.getJavaProject().getProject();

          }
          
          if ((newProj != null) && (newProj != proj)) {
            proj = newProj;
            
            fViewer.setInput(new IProject[] {proj});
            fViewer.expandToLevel(2);
          }
        }
      }
    }
    
  }


  /**
   * Create the button to evaluate a goal.
   * @param parent the parent where to put the button
   */
  private void createButtons(final Composite parent) {
    final ToolBar tb = new ToolBar(parent, SWT.HORIZONTAL);
    fBtnEvaluate = new ToolItem(tb, SWT.PUSH);
    fBtnEvaluate.setImage(Utils.createImage("icons/reevaluate.gif"));
    fBtnEvaluate.setEnabled(false);
    fBtnEvaluate.setToolTipText("Build the selected file");
    fBtnEvaluate.addSelectionListener(this);
  }
  
  /** {@inheritDoc} */
  public void createPartControl(final Composite parent) {  
    final GridLayout rl = new GridLayout(1, false);
    parent.setLayout(rl);
    createButtons(parent);
    createViewer(parent);
    
    final IWorkbench wb = PlatformUI.getWorkbench();
    wb.getActiveWorkbenchWindow().addPageListener(this);

  }

  /** {@inheritDoc} */
  public void setFocus() { }


  /** {@inheritDoc} */
  public void doubleClick(final DoubleClickEvent event) {
    if (fSel instanceof IShowable) {
      ((IShowable) fSel).show();
    }
  }


  /** {@inheritDoc} */
  public void selectionChanged(final SelectionChangedEvent event) {
    final ITreeSelection ts = (ITreeSelection) fViewer.getSelection();
    final Object o = ts.getFirstElement();
    if (o instanceof AWorkspaceElement) {
      fSel = (AWorkspaceElement) o;
      fViewer.refresh(o);
      fBtnEvaluate.setEnabled(fSel.isEvaluateEnabled());
    }
    else {
      fBtnEvaluate.setEnabled(false);
    }
  }

  /** {@inheritDoc} */
  public void widgetSelected(final SelectionEvent e) {
    final Job j = new Job("Evaluating the goals...") {
      protected IStatus run(final IProgressMonitor monitor) {
        if (fSel instanceof AWorkspaceElement) {
          ((AWorkspaceElement)fSel).compile(fViewer);
        }
        return Utils.getOkStatus();
      }
    };
    j.schedule();      
  }


  /** {@inheritDoc} */
  public void widgetDefaultSelected(final SelectionEvent e) { }

  @Override
  public void pageActivated(IWorkbenchPage page) {
    page.addSelectionListener(new MySelListener());

    //System.out.println("hi");    
  }

  @Override
  public void pageClosed(IWorkbenchPage page) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void pageOpened(IWorkbenchPage page) {
    // TODO Auto-generated method stub
    System.out.println("hoy");    
  }



}
