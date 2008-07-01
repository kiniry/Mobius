package mobius.directVCGen.ui.poview;

import mobius.directVCGen.ui.poview.tree.IShowable;
import mobius.directVCGen.ui.poview.tree.AProofElement;
import mobius.directVCGen.ui.poview.tree.AWorkspaceElement;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
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
import org.eclipse.ui.part.ViewPart;


public class ProjectProofs extends ViewPart implements IDoubleClickListener, ISelectionChangedListener, SelectionListener {
  /** the current selection. */
  private AWorkspaceElement fSel;
  /** the tree showing all the proofs. */
  private TreeViewer fViewer;
  /** the button that triggers the evaluate action. */
  private ToolItem fBtnEvaluate;
  

  
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
    fViewer.setInput(AWorkspaceElement.createProjectItem(Utils.getProjects()));
    fViewer.addDoubleClickListener(this);
    fViewer.addSelectionChangedListener(this);
  }





  private void createButtons(final Composite parent) {
    final ToolBar tb = new ToolBar(parent, SWT.HORIZONTAL);
    fBtnEvaluate = new ToolItem(tb, SWT.PUSH);
    fBtnEvaluate.setImage(Utils.createImage("icons/reevaluate.gif"));
    fBtnEvaluate.setEnabled(false);
    fBtnEvaluate.setToolTipText("Try to evaluate the goals");
    fBtnEvaluate.addSelectionListener(this);
  }
  
  /** {@inheritDoc} */
  public void createPartControl(final Composite parent) {  
    final GridLayout rl = new GridLayout(1, false);
    parent.setLayout(rl);
    createButtons(parent);
    createViewer(parent);
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
      fBtnEvaluate.setEnabled(fSel instanceof AProofElement);
    }
    else {
      fBtnEvaluate.setEnabled(false);
    }
  }

  /** {@inheritDoc} */
  public void widgetSelected(final SelectionEvent e) {
    final Job j = new Job("Evaluating the goals...") {
      protected IStatus run(final IProgressMonitor monitor) {
        if (fSel instanceof AProofElement) {
          ((AProofElement)fSel).compile(fViewer);
        }
        return Utils.getOkStatus();
      }
    };
    j.schedule();      
  }


  /** {@inheritDoc} */
  public void widgetDefaultSelected(final SelectionEvent e) { }
    


}
