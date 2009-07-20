package mobius.directvcgen.ui.poview;

import mobius.directvcgen.ui.poview.tree.AWorkspaceElement;
import mobius.directvcgen.ui.poview.tree.IShowable;
import mobius.directvcgen.ui.poview.util.ImagesUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IJavaElement;
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
 * This class represents the proof obligation viewer.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ProjectProofs extends ViewPart 
  implements IDoubleClickListener, ISelectionChangedListener, 
             SelectionListener, IPageListener {
  
  /** the current instance of the ProjectProofs. */
  private static ProjectProofs instance; 
  
  /** the current selection. */
  private AWorkspaceElement fSel;
  /** the tree showing all the proofs. */
  private TreeViewer fViewer;
  /** the button that triggers the evaluate action. */
  private ToolItem fBtnEvaluate;
  
  /**
   * Creates a new view.
   */
  public ProjectProofs() {
    instance = this;
  }
  
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
    // sets the initial input
    //fViewer.setInput(new IProject[0]);
//    fViewer.setInput(Utils.getProjects());
    fViewer.addDoubleClickListener(this);
    fViewer.addSelectionChangedListener(this);
    fViewer.setInput(new IProject[] {});

  }




  /**
   * Create the button to evaluate a goal.
   * @param parent the parent where to put the button
   */
  private void createButtons(final Composite parent) {
    final ToolBar tb = new ToolBar(parent, SWT.HORIZONTAL);
    fBtnEvaluate = new ToolItem(tb, SWT.PUSH);
    fBtnEvaluate.setImage(ImagesUtils.createImage("icons/reevaluate.gif"));
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
        return ImagesUtils.getOkStatus();
      }
    };
    j.schedule();      
  }


  /** {@inheritDoc} */
  public void widgetDefaultSelected(final SelectionEvent e) { }

  /** {@inheritDoc} */
  public void pageActivated(final IWorkbenchPage page) {
    page.addSelectionListener(new MySelListener(page.getSelection()));
  }

  /** {@inheritDoc} */
  public void pageClosed(final IWorkbenchPage page) {
  }

  /** {@inheritDoc} */
  public void pageOpened(final IWorkbenchPage page) {
  }

  /**
   * Returns the current instance of the view.
   * @return the last registered instance of the view
   */
  public static ProjectProofs getDefault() {
    return instance;
  }

  /**
   * Returns the tree viewer associated with the view.
   * @return null if called before the first call to 
   * {@link #createPartControl(Composite)} afterward returns 
   * a valid tree viewer.
   */
  public TreeViewer getViewer() {
    return fViewer;
  }
  
  /**
   * A listener that is used to change the project presented in the tree viewer
   * when another project has focus in the package viewer.
   * @author J. Charles (julien.charles@inria.fr)
   */
  private class MySelListener implements ISelectionListener {
    /** the currently selected project. */
    private IProject fProj;
    
    public MySelListener(ISelection selection) {
      selectionChanged(selection);
    }
    public void selectionChanged(final ISelection selection) {
      if (selection instanceof IStructuredSelection) {
        final IStructuredSelection sel = (IStructuredSelection) selection;
        if (sel.size() == 1) {
          //System.out.println(sel);
          final Object o = sel.getFirstElement();
          IProject newProj = null;
          if (o instanceof IProject) {
            newProj = (IProject) o;
          } 
          else if (o instanceof IJavaElement) {
            final IJavaElement elem = (IJavaElement) o;
            newProj = elem.getJavaProject().getProject();

          } 
          else if (o instanceof IResource) {
            final IResource res = (IResource) o;
            newProj = res.getProject();
          }
          
          if ((newProj != null) && (newProj != fProj)) {
            fProj = newProj;
            //System.out.println(newProj);
            fViewer.setInput(new IProject[] {fProj});
            fViewer.refresh(true);
            //fViewer.add(fProj, fProj);
            fViewer.expandToLevel(2);
          }
          else if (fProj == null) {
            fViewer.setInput(new IProject[] {});
          }
        }
      }     
    }
    
    /** {@inheritDoc} */
    public void selectionChanged(final IWorkbenchPart part, final ISelection selection) {
      selectionChanged(selection);
    }
    
  }

}
