//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jack.plugin.perspective;

import jack.plugin.JackPlugin;
import jack.plugin.JpovUtil;
import jack.plugin.edit.EditedFile;
import jack.plugin.edit.IEditedFile;
import jack.plugin.prove.ProofTask;
import jack.plugin.prove.ProveAction;
import jack.util.Logger;

import java.io.IOException;
import java.util.Enumeration;

import jml2b.languages.Languages;
import jpov.Icons;
import jpov.JpoFile;
import jpov.viewer.tree.TreeContentProvider;
import jpov.viewer.tree.TreeFilter;
import jpov.viewer.tree.TreeFilterWindow;
import jpov.viewer.tree.TreeItemSelection;
import jpov.viewer.tree.TreeLabelProvider;
import jpov.viewer.tree.TreeSorter;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.ViewForm;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.ProgressBar;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.ViewPart;

/**
 * View containing the cases explorer.
 * 
 * @author L. Burdy
 **/
public class CaseExplorer extends ViewPart implements ICaseExplorer {

	JpoFile jpoFile;

	/**
	 * The main composite containing the different objects
	 **/
	private Composite leftComp;

	/**
	 * The progress bar that indicates the proof percentage.
	 **/
	private ProgressBar proofPb;

	/**
	 * The selection changed lister for the tree
	 */
	protected TreeItemSelection ehl;

	TreeFilterWindow tfw;

	/** 
	 * The viewform that contains the tree. 
	 **/
	protected ViewForm treeForm;

	/** 
	 * The tree. 
	 **/
	private TreeViewer tree;

	FlatAction flatAction;
	HierarchyAction hierachyAction;
	Menu goalMenu = null;
	Menu caseMenu = null;

	private Menu multipleGoalMenu;
	
	
	public void createPartControl(Composite parent) {
		leftComp = new Composite(parent, SWT.NULL);

		// layout with 6 columns
		GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 6;
		gridLayout.marginWidth = 0;
		leftComp.setLayout(gridLayout);

		// constructs the proof progress bar that fills 6 columns
		proofPb = new ProgressBar(leftComp, SWT.HORIZONTAL | SWT.SMOOTH);
		proofPb.setMaximum(100);
		proofPb.setSelection(0);
		proofPb.setBackground(new Color(null, 255, 0, 0));
		proofPb.setForeground(new Color(null, 0, 255, 0));
		GridData gridData = new GridData();
		gridData.horizontalSpan = 6;
		gridData.horizontalAlignment = GridData.FILL;
		proofPb.setLayoutData(gridData);

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

		// Creates the tree filter
		tfw = new TreeFilterWindow(getSite().getShell(), this);
		getViewSite().getActionBars().getToolBarManager().add(
			new TreeFilterAction(tfw));
		TreeFilter filter = new TreeFilter(tfw);

		// Construct the tree
		tree = new TreeViewer(treeForm, SWT.MULTI);
		// Sets the content provider
		tree.setContentProvider(new TreeContentProvider(this));
		// Sets the label provider
		tree.setLabelProvider(new TreeLabelProvider(this));
		// Sets the sorter
		tree.setSorter(new TreeSorter(this));
		// Sets the filster
		tree.addFilter(filter);
		// Fills the tree
		//		constructTree(pov);
	 
		MenuManager mm =
			(MenuManager) getViewSite().getActionBars().getMenuManager();
		MenuManager smm = new MenuManager("Layout");

		flatAction = new FlatAction(tree);
		flatAction.setChecked(true);
		hierachyAction = new HierarchyAction(tree);
		smm.add(flatAction);
		smm.add(hierachyAction);
		mm.add(new Separator());
		mm.add(smm);
		goalMenu = createTreeGoalMenu();
		caseMenu = createTreeCaseMenu();
		multipleGoalMenu = createTreeMultipleGoalMenu();
		tree.getControl().setMenu(caseMenu);
		treeForm.setContent(tree.getControl());
		

	}

	Menu createTreeGoalMenu() {
		ExpandAction foldAction = new ExpandAction(true, this);
		ExpandAction unFoldAction = new ExpandAction(false, this);
		CheckAction checkedAction = new CheckAction(this);
		UncheckAction uncheckedAction = new UncheckAction(this);

		// Create menu manager.
		MenuManager menuMgr = new MenuManager();

		menuMgr.add(new Separator());
		menuMgr.add(new Separator());
		menuMgr.add(checkedAction);
		menuMgr.add(uncheckedAction);
		menuMgr.add(foldAction);
		menuMgr.add(unFoldAction);
		menuMgr.add(new Separator());
		
		MenuManager prove = new MenuManager("Prove");
		Enumeration e = Languages.getLanguagesNames();
		while (e.hasMoreElements()) {
			String element = (String) e.nextElement();
			if (Languages.getInteractiveProverClass(element) != null)
			prove.add(Languages.getInteractiveProverClass(element).factory(this));
				
		}
		
		menuMgr.add(prove);

		// Create menu.
		return menuMgr.createContextMenu(getTree().getControl());

	}
	Menu createTreeCaseMenu() {
		ExpandAction foldAction = new ExpandAction(true, this);
		ExpandAction unFoldAction = new ExpandAction(false, this);
		CheckAction checkedAction = new CheckAction(this);
		UncheckAction uncheckedAction = new UncheckAction(this);

		// Create menu manager.
		MenuManager menuMgr = new MenuManager();

		menuMgr.add(new Separator());
		menuMgr.add(new Separator());
		menuMgr.add(checkedAction);
		menuMgr.add(uncheckedAction);
		menuMgr.add(foldAction);
		menuMgr.add(unFoldAction);
		menuMgr.add(new Separator());
		
		MenuManager prove = new MenuManager("Prove Automatically");
		/*Enumeration e = Languages.getProofTaskClasses();
		while (e.hasMoreElements()) {

			ProofTask pt = (ProofTask) e.nextElement(); 
			//Logger.get().println(pt);
			if (pt != null) {
				prove.add(new ProofAction(pt.factory(), this));
			}
				
		}*/
		
		menuMgr.add(prove);
		
		// Create menu.
		return menuMgr.createContextMenu(getTree().getControl());

	}
	Menu createTreeMultipleGoalMenu() {
		ExpandAction foldAction = new ExpandAction(true, this);
		ExpandAction unFoldAction = new ExpandAction(false, this);
		CheckAction checkedAction = new CheckAction(this);
		UncheckAction uncheckedAction = new UncheckAction(this);

		// Create menu manager.
		MenuManager menuMgr = new MenuManager();

		menuMgr.add(new Separator());
		menuMgr.add(new Separator());
		menuMgr.add(checkedAction);
		menuMgr.add(uncheckedAction);
		menuMgr.add(foldAction);
		menuMgr.add(unFoldAction);
		menuMgr.add(new Separator());
		
		MenuManager prove = new MenuManager("Prove Automatically");
		Enumeration e = Languages.getProofTaskClasses();
		while (e.hasMoreElements()) {

			ProofTask pt = (ProofTask) e.nextElement(); 
			//Logger.get().println(pt);

			if (pt != null) {
				ProveAction p = pt.factory();
				p.setText(p.toString());
				p.setCaseViewer(this);
				prove.add(p);
			}
				
		}
		
		menuMgr.add(prove);
		
		// Create menu.
		return menuMgr.createContextMenu(getTree().getControl());

	}
	public JpoFile getJpoFile() {
		return this.jpoFile;
	}
	
	
	/**
	 * Sets the input of the tree to a jpo file
	 * @param pov The jpo file
	 **/
	private void constructTree() {
		if (jpoFile != null && jpoFile.getJmlFile() != null) {
			tree.setInput(jpoFile.getJmlFile());
		} else
			tree.setInput(null);

	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPart#setFocus()
	 */
	public void setFocus() {
	}

	/** 
	 * Display the following error message using the appropriate title window.
	 */
	public void errorMessage(String message) {
		MessageDialog.openError(getSite().getShell(), "Jack JML View", message);
	}

	/**
	 * Clear the viewed file.
	 */
	public void clearViewedFile(ICompilationUnit javaSource) {
		jpoFile = null;
		//javaSource = null;
		updateContent(javaSource == null ? null : javaSource.getResource().getName());
	}

	/**
	 * Sets the currently viewed file.
	 * This method returns true on success and false otherwise..
	 */
	public boolean setViewedFile(
		ICompilationUnit compilation_unit,
		SourceCaseViewer ce) {

		IEditedFile jpo_file = new EditedFile(JackPlugin.getJpoFile(compilation_unit));
		if (jpo_file != null) {
			try {
				if (jpoFile != null) {
					jpoFile = null;
					updateLeftComp();
				}
				jpoFile = JpovUtil.loadJpoFile(jpo_file);
			} catch (Exception e) {
				errorMessage("Exception catched : " + e.toString());
				clearViewedFile(compilation_unit);
				return true;
			}
		} else {
			// no jpo file
			jpoFile = null;
		}
		updateContent(compilation_unit == null ? null : compilation_unit.getResource().getName());
		ce.setDocument((IFile) compilation_unit.getResource(), ehl);
		ce.updateTitle(jpoFile);
		return true;
	}

//	public boolean setViewedFile(
//			IFile jpo_file,
//			SourceCaseViewer ce) {
//
//			if (jpo_file != null) {
//				try {
//					if (jpoFile != null) {
//						jpoFile = null;
//						updateLeftComp();
//					}
//					jpoFile = JpovUtil.loadJpoFile(jpo_file);
//				} catch (Exception e) {
//					errorMessage("Exception catched : " + e.toString());
////					clearViewedFile(jpo_file);
//					return true;
//				}
//			} else {
//				// no jpo file
//				jpoFile = null;
//			}
//			updateContent(jpoFile == null ? null : jpoFile.getName());
//			ce.setDocument(jpoFile.getJmlFile().getFileName());
//			ce.updateTitle(jpoFile);
//			return true;
//		}
	
	public boolean setViewedFile(
			IEditedFile jpo_file,
			SourceCaseViewer ce) {

			if (jpo_file != null) {
				try {
					if (jpoFile != null) {
						jpoFile = null;
						updateLeftComp();
					}
					jpoFile = JpovUtil.loadJpoFile(jpo_file);
				} catch (Exception e) {
					errorMessage("Exception catched : " + e.toString());
//					clearViewedFile(jpo_file);
					return true;
				}
			} else {
				// no jpo file
				jpoFile = null;
			}
			updateContent(jpoFile == null ? null : jpoFile.getName());
			ce.setDocument(jpoFile.getJmlFile().getFileName());
			ce.updateTitle(jpoFile);
			return true;
		}
	/**
	 * Update the content of the window depending on the values of
	 * jpoFile and javaFile.
	 */
	void updateContent(String javaSource) {
		if (ehl != null)
			tree.removeSelectionChangedListener(ehl);
		try {
			// Creates the tree selection changed listener
			if (javaSource != null)
			ehl =
				new TreeItemSelection(
					(LemmaViewer) getSite().getPage().showView(
						JackPlugin.LEMMA_VIEWER),
					(SourceCaseViewer) getSite().getPage().showView(
						JackPlugin.SOURCE_CASE_VIEWER_ID), this);
		} catch (PartInitException e) {
			MessageDialog.openError(
				getSite().getShell(),
				JackPlugin.DIALOG_TITLE,
				"Error showing view: " + e.toString());
			return;
		}
		// Sets the selection changed listener
		tree.addSelectionChangedListener(ehl);

		updateLeftComp();
		updateTitle(javaSource);
	}

	/**
	 * Update the title of the window depending on the variables
	 * javaFile and jpoFile.
	 */
	private void updateTitle(String javaSource) {
		String title = "Case Explorer - ";
		if (javaSource != null) {
			title += javaSource;
			if (jpoFile == null) {
				title += " (Not compiled, use JML Compile)";
			}
		}
		setPartName(title);
	}

	/**
	 * Updates the view from a new jpo file
	 * @param pov The new jpo file
	 **/
	public void updateLeftComp() {
		constructTree();
		if (jpoFile != null) {
			int nbPo = jpoFile.getJmlFile().getNbPo();
			int proved = jpoFile.getJmlFile().getNbPoProved();

			String t = "Case Explorer - ";
			t += jpoFile.getJpoName();
			t += " - Lemma: "
				+ nbPo
				+ " Proved: "
				+ proved
				+ "("
				+ (nbPo == 0 ? 100 : ((proved * 100) / nbPo))
				+ ")";
			setPartName(t);
			proofPb.setSelection(nbPo == 0 ? 100 : (proved * 100) / nbPo);
			leftComp.redraw();
			tree.refresh();

		}
	}

	/**
	 * Updates the view
	 **/
	public void displayStatus() {
		updateLeftComp();
	}

	/**
	 * @return
	 */
	public TreeItemSelection getEhl() {
		return ehl;
	}

	/**
	 * @return
	 */
	public TreeViewer getTree() {
		return tree;
	}

	/**
	 * Returns the selected items
	 **/
	public Object[] getTreeSelection() {
		return ((StructuredSelection) tree.getSelection()).toArray();
	}

	/* (non-Javadoc)
	 * @see jack.plugin.perspective.ICaseExplorer#save()
	 */
	public void save() throws IOException {
		if (jpoFile != null){
			jpoFile.finalizeLoad();
			jpoFile.save();
			SourceCaseViewer editor;
			try {
				editor =
					(SourceCaseViewer) getSite().getPage().showView(
							JackPlugin.SOURCE_CASE_VIEWER_ID);

			} catch (PartInitException e) {
				MessageDialog.openError(
						getSite().getShell(),
						JackPlugin.DIALOG_TITLE,
						"Error showing view: " + e.toString());
				return;
			}
			editor.updateTitle(jpoFile);
		}
	}

	public int getLayout() {
		if (flatAction.isChecked())
			return FLAT;
		else
			return HIERARCHY;
	}

	/* (non-Javadoc)
	 * @see jack.plugin.perspective.ICaseExplorer#setGoalMenu()
	 */
	public void setGoalMenu() {
		// TODO Auto-generated method stub
		tree.getControl().setMenu(goalMenu);
		
	}

	/* (non-Javadoc)
	 * @see jack.plugin.perspective.ICaseExplorer#setLemmaMenu()
	 */
	public void setLemmaMenu() {
		// TODO Auto-generated method stub
		tree.getControl().setMenu(caseMenu);
	}

	/* (non-Javadoc)
	 * @see jack.plugin.perspective.ICaseExplorer#setMultipleGoalMenu()
	 */
	public void setMultipleGoalMenu() {
		// TODO Auto-generated method stub
		tree.getControl().setMenu(multipleGoalMenu);
	}

}

/**
 * This action opens the filter dialog.
 *
 *  @author L. Burdy
 **/
class TreeFilterAction extends Action {

	TreeFilterWindow tfw;

	TreeFilterAction(TreeFilterWindow tfw) {
		this.tfw = tfw;
		setImageDescriptor(Icons.FILTER_DESCRIPTOR);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.action.IAction#run()
	 */
	public void run() {
		tfw.open();
	}

}


/**
 * This action allows to fold or unfold a node.
 *
 *  @author L. Burdy
 **/
class ExpandAction extends Action {

	final boolean expand;
	ICaseExplorer explorer;

	ExpandAction(boolean expand, ICaseExplorer ex) {
		explorer = ex;
		if (this.expand = expand) {
			setText("Fold");
			setToolTipText("Fold the selected subtree");
		} else {
			setText("Unfold");
			setToolTipText("Unfold the selected subtree");
		}
	}

	public void expand(Object ti) {
		explorer.getTree().setExpandedState(ti, expand);
		Object[] tis =
			(
				(ITreeContentProvider) explorer
					.getTree()
					.getContentProvider())
					.getChildren(
				ti);
		for (int i = 0; i < tis.length; i++)
			expand(tis[i]);
	}

	public void run() {
		// get the selection
		Object[] tis = explorer.getTreeSelection();

		for (int i = 0; i < tis.length; i++)
			expand(tis[i]);
		explorer.getTree().refresh();
	}
}

/**
 * This action allows to mark a goal as "checked".
 *
 *  @author L. Burdy
 **/
class CheckAction extends Action {

	CaseExplorer explorer;

	CheckAction(CaseExplorer ex) {
		explorer = ex;
		setText("Checked");
	}

	public void run() {
		// get the selection
		Object[] tis = explorer.getTreeSelection();

		for (int i = 0; i < tis.length; i++)
			 ((jpov.structure.TreeObject) tis[i]).setChecked();
		explorer.getTree().refresh();
		try {
			explorer.save();
		} catch (IOException ex) {
			Logger.err.println(ex.toString());
		}
	}
}

/**
 * This action allows to mark a goal as unchecked. 
 *
 *  @author L. Burdy
 **/
class UncheckAction extends Action {

	CaseExplorer explorer;

	UncheckAction(CaseExplorer ex) {
		explorer = ex;
		setText("Unchecked");
	}

	public void run() {
		// get the selection
		Object[] tis = explorer.getTreeSelection();

		for (int i = 0; i < tis.length; i++)
			 ((jpov.structure.TreeObject) tis[i]).setUnchecked();
		explorer.getTree().refresh();
		try {
			explorer.save();
		} catch (IOException ex) {
			Logger.err.println(ex.toString());
		}
	}
}

/**
 * This action sets the layout to flat. 
 *
 *  @author L. Burdy
 **/
class FlatAction extends Action {

	TreeViewer t;

	FlatAction(TreeViewer t) {
		super("Flat", Action.AS_RADIO_BUTTON);
		this.t = t;
	}

	public void run() {
		t.refresh();
	}
}

/**
 * This action sets the layout to hierachycal
 *
 *  @author L. Burdy
 **/
class HierarchyAction extends Action {

	TreeViewer t;

	HierarchyAction(TreeViewer t) {
		super("Hierarchical", Action.AS_RADIO_BUTTON);
		this.t = t;
	}

	public void run() {
		t.refresh();
	}
}