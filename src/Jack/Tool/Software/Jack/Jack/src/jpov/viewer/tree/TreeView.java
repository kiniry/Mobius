//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Tree.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.tree;

import jpov.JpoFile;
import jpov.viewer.JpovViewer;

import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.ViewForm;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.ProgressBar;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.ToolItem;

/**
 * This class implements the left part of the viewer containing the status of
 * the file and the tree to select goals.
 * @author burdy
 */
public class TreeView {

	/**
	 * @return a grid data with the flag <code>grabExcessHorizontalSpace</code>
	 * set
	 */
	private static GridData gridData1() {
		GridData gd = new GridData();
		gd.grabExcessHorizontalSpace = true;
		return gd;
	}

	/**
	 * The main composite containing the different objects
	 **/
	private Composite leftComp;

	/**
	 * The progress bar that indicates the proof percentage.
	 **/
	private ProgressBar proofPb;

	/**
	 * The label indicating the number of proof obligation.
	 **/
	private Label nbPoLabel;

	/**
	 * The label indicating the proof percentage
	 */
	private Label percent;

	/**
	 * The label indicating the number of proved proof obligations
	 */
	private Label provedLabel;

	/**
	 * The label indicating the number of unproved proof obligations
	 */
	private Label unProvedLabel;

	/**
	 * The selection changed lister for the tree
	 */
	protected TreeItemSelection ehl;

	/** 
	 * The viewform that contains the tree. 
	 **/
	protected ViewForm treeForm;

	/** 
	 * The tree. 
	 **/
	private TreeViewer tree;
	JpovViewer viewer;
	/**
	 * Constructs the left part of the view.
	 * It contains six columns:
	 * <pre>
	 * |<-                        the progress bar                           ->|
	 * |                 Goals :|n          |                      p|%         |
	 * |     p_icon|Proved :    |pr         |     u_icon|Unproved : |un        |
	 * |<-                            the tree                               ->| 
	 * </pre>
	 * where
	 * <UL>
	 * <li> n is the number of PO
	 * <li> p is the proof percentage
	 * <li> pr is the number of proved PO
	 * <li> un ids the number of unproved PO
	 * <li> p_icon is the proved icon
	 * <li> u_icnon is the unporved icon
	 * </UL>   
	 * @param sform The containing form
	 * @param pov The currently displayed jpo file
	 * @param viewer The current viewer
	 **/
	public TreeView(SashForm sform, JpoFile pov, JpovViewer viewer) {
		leftComp = new Composite(sform, SWT.NONE);

		// layout with 6 columns
		GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 6;
		gridLayout.marginWidth = 0;
		leftComp.setLayout(gridLayout);

		// constructs the proof progress bar that fills 6 columns
		proofPb = new ProgressBar(leftComp, SWT.HORIZONTAL | SWT.SMOOTH);
		proofPb.setMaximum(100);
		proofPb.setSelection(0);
		proofPb.setBackground(new Color(JpovViewer.getDisplay(), 255, 0, 0));
		proofPb.setForeground(new Color(JpovViewer.getDisplay(), 0, 255, 0));
		GridData gridData = new GridData();
		gridData.horizontalSpan = 6;
		gridData.horizontalAlignment = GridData.FILL;
		proofPb.setLayoutData(gridData);

		// Constructs a "Goals :" label on two columns right aligned
		Label nbPoText = new Label(leftComp, SWT.HORIZONTAL);
		nbPoText.setText("Goals :");
		gridData = new GridData();
		gridData.horizontalSpan = 2;
		gridData.grabExcessHorizontalSpace = true;
		gridData.horizontalAlignment = GridData.END;
		nbPoText.setLayoutData(gridData);

		// Constructs the label containing the number of PO on 1 column left
		// aligned
		nbPoLabel = new Label(leftComp, SWT.HORIZONTAL);
		nbPoLabel.setLayoutData(gridData1());

		// Constructs the label containing the percentage of proved PO on 2 
		// columns right aligned
		percent = new Label(leftComp, SWT.HORIZONTAL);
		gridData = new GridData();
		gridData.horizontalSpan = 2;
		gridData.grabExcessHorizontalSpace = true;
		gridData.horizontalAlignment = GridData.END;
		percent.setLayoutData(gridData);

		// Constructs a "%" label on one column left aligned
		Label percentText = new Label(leftComp, SWT.HORIZONTAL);
		percentText.setText("%");
		percentText.setLayoutData(gridData1());

		// Constructs an image with the proved icon on one column right aligned
		Label provedImage = new Label(leftComp, SWT.HORIZONTAL);
		provedImage.setImage(JpovViewer.PROVED);
		gridData = new GridData();
		gridData.grabExcessHorizontalSpace = true;
		gridData.horizontalAlignment = GridData.END;
		provedImage.setLayoutData(gridData);

		// Constructs a "Proved :" label on one column left aligned
		Label provedText = new Label(leftComp, SWT.HORIZONTAL);
		provedText.setText("Proved :");
		provedText.setLayoutData(gridData1());

		// Constructs the label containing the number of proved PO on 1 column 
		// left aligned
		provedLabel = new Label(leftComp, SWT.HORIZONTAL);
		provedLabel.setLayoutData(gridData1());

		// Constructs an image with the unproved icon on one column right 
		// aligned
		Label unProvedImage = new Label(leftComp, SWT.HORIZONTAL);
		unProvedImage.setImage(JpovViewer.UNPROVED);
		gridData = new GridData();
		gridData.grabExcessHorizontalSpace = true;
		gridData.horizontalAlignment = GridData.END;
		unProvedImage.setLayoutData(gridData);

		// Constructs a "Unproved :" label on one column left aligned
		Label unProvedText = new Label(leftComp, SWT.HORIZONTAL);
		unProvedText.setText("Unproved :");
		unProvedText.setLayoutData(gridData1());

		// Constructs the label containing the number of unproved PO on 1 column 
		// left aligned
		unProvedLabel = new Label(leftComp, SWT.HORIZONTAL);
		unProvedLabel.setLayoutData(gridData1());

		// Constructs the tree form on 6 columns.
		treeForm =
			new ViewForm(leftComp, SWT.H_SCROLL | SWT.V_SCROLL | SWT.BORDER);

		gridData = new GridData();
		gridData.horizontalAlignment = GridData.FILL;
		gridData.verticalAlignment = GridData.FILL;
		gridData.horizontalSpan = 6;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		treeForm.setLayoutData(gridData);

		// Creates the tree selection changed listener
		ehl = new TreeItemSelection(viewer, viewer, viewer);

		// Creates the tree filter
		TreeFilter filter = new TreeFilter(constructTreeToolBar(viewer));

		// Construct the tree
		tree = new TreeViewer(treeForm, SWT.NULL);
		// Sets the content provider
		tree.setContentProvider(new TreeContentProvider(viewer));
		// Sets the label provider
		tree.setLabelProvider(new TreeLabelProvider(viewer));
		// Sets the sorter
		tree.setSorter(new TreeSorter(viewer));
		// Sets the filster
		tree.addFilter(filter);
		// Sets the selection changed listener
		tree.addSelectionChangedListener(ehl);
		// Fills the tree
		constructTree(pov);
		treeForm.setContent(tree.getControl());
	}

	/**
	 * Sets the input of the tree to a jpo file
	 * @param pov The jpo file
	 **/
	private void constructTree(JpoFile pov) {
		if (pov != null && pov.getJmlFile() != null) {
			tree.setInput(pov.getJmlFile());
		}
	}

	/**
	 * Constructs the tree tool bar. The tool bar contains a button to open
	 * the filter window.
	 * @param viewer The current viewer
	 * @return the associated tree filter window
	 */
	private TreeFilterWindow constructTreeToolBar(JpovViewer viewer) {
		
		ToolBar toolbar = new ToolBar(treeForm, SWT.HORIZONTAL);
		treeForm.setTopRight(toolbar);
		ToolItem ti = new ToolItem(toolbar, SWT.FLAT);
		ti.setImage(JpovViewer.FILTER);
		// Create the tree filter window
		final TreeFilterWindow tfw =
			new TreeFilterWindow(viewer.getShell(), viewer);
		// Add a listener to the button that open the tree filter window    
		ti.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {
			}
			public void widgetSelected(SelectionEvent e) {
				tfw.open();
			}
		});
		return tfw;
	}

	/**
	 * Updates the view from a new jpo file
	 * @param pov The new jpo file
	 **/
	public void updateLeftComp(JpoFile pov) {
		constructTree(pov);
		if (pov != null) {
			int nbPo = pov.getJmlFile().getNbPo();
			int proved =
				pov.getJmlFile().getNbPoProved();

			nbPoLabel.setText(nbPo + "");
			provedLabel.setText(proved + "");
			unProvedLabel.setText((nbPo - proved) + "");
			percent.setText((nbPo == 0 ? 100 : ((proved * 100) / nbPo)) + "");
			proofPb.setSelection(nbPo == 0 ? 100 : (proved * 100) / nbPo);
			leftComp.redraw();
			tree.refresh();
		}
	}

	/**
	 * Sets the input of the tree to <code>null</code>.
	 **/
	public void eraseInput() {
		tree.setInput(null);
	}

	/**
	 * Returns the selection changed lister for the tree.
	 * @return <code>ehl</code>
	 **/
	public TreeItemSelection getEhl() {
		return ehl;
	}

	/**
	 * Returns the tree
	 * @return <code>tree</code>
	 **/
	public TreeViewer getTree() {
		return tree;
	}

	/**
	 * Returns the selected items
	 **/
	public Object[] getTreeSelection() {
		return ((StructuredSelection) tree.getSelection()).toArray();
	}

	/**
	 * Returns the viewform that contains the tree.
	 * @return <code>treeForm</code>
	 */
	public ViewForm getTreeForm() {
		return treeForm;
	}

}
