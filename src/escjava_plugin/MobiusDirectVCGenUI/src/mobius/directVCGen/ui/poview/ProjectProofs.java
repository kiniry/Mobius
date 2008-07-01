package mobius.directVCGen.ui.poview;

import mobius.directVCGen.ui.poview.tree.IShowable;
import mobius.directVCGen.ui.poview.tree.ProofElement;
import mobius.directVCGen.ui.poview.tree.WorkspaceElement;

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
	/** the current selection */
	private WorkspaceElement selection = null;
	/** the tree showing all the proofs */
	private TreeViewer viewer;
	/** the button that triggers the evaluate action */
	private ToolItem btnEvaluate;
	

	
    private void createViewer(Composite parent) {
    	GridData gd = new GridData();
    	gd.horizontalAlignment = GridData.FILL;
    	gd.grabExcessHorizontalSpace = true;
    	gd.verticalAlignment = GridData.FILL;
    	gd.grabExcessVerticalSpace = true;
        viewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL
                | SWT.V_SCROLL);
        viewer.getControl().setLayoutData(gd);
        viewer.setUseHashlookup(true);
        viewer.setContentProvider(new POsContentProvider(viewer));
        viewer.setLabelProvider(new POsLabelProvider());
        viewer.setInput(WorkspaceElement.createProjectItem(Utils.getProjects()));
        viewer.addDoubleClickListener(this);
        viewer.addSelectionChangedListener(this);
    }





	private void createButtons(Composite parent) {
		ToolBar tb = new ToolBar(parent, SWT.HORIZONTAL);
    	btnEvaluate = new ToolItem(tb, SWT.PUSH);
    	btnEvaluate.setImage(Utils.createImage("icons/reevaluate.gif"));
    	btnEvaluate.setEnabled(false);
    	btnEvaluate.setToolTipText("Try to evaluate the goals");
    	btnEvaluate.addSelectionListener(this);
	}
	
	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	public void createPartControl(Composite parent) {	
		GridLayout rl = new GridLayout(1, false);
    	parent.setLayout(rl);
    	createButtons(parent);
		createViewer(parent);
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	public void setFocus() {}


	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IDoubleClickListener#doubleClick(org.eclipse.jface.viewers.DoubleClickEvent)
	 */
	public void doubleClick(DoubleClickEvent event) {
		if(selection instanceof IShowable) {
			((IShowable) selection).show();
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ISelectionChangedListener#selectionChanged(org.eclipse.jface.viewers.SelectionChangedEvent)
	 */
	public void selectionChanged(SelectionChangedEvent event) {
		ITreeSelection ts = (ITreeSelection) viewer.getSelection();
		Object o = ts.getFirstElement();
		if(o instanceof WorkspaceElement) {
			selection = (WorkspaceElement) o;
			viewer.refresh(o);
			btnEvaluate.setEnabled(selection instanceof ProofElement);
		}
		else {
			btnEvaluate.setEnabled(false);
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.swt.events.SelectionListener#widgetSelected(org.eclipse.swt.events.SelectionEvent)
	 */
	public void widgetSelected(SelectionEvent e) {
		Job j = new Job("Evaluating the goals...") {
			protected IStatus run(IProgressMonitor monitor) {
				if(selection instanceof ProofElement) {
					((ProofElement)selection).compile(viewer);
				}
				return Utils.getOkStatus();
			}
		};
		j.schedule();			
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org.eclipse.swt.events.SelectionEvent)
	 */
	public void widgetDefaultSelected(SelectionEvent e) {}
		


}
