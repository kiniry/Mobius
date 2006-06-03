//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JpovViewer.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer;

import jack.plugin.perspective.ICaseExplorer;
import jack.plugin.perspective.ILemmaViewer;
import jack.plugin.perspective.ISourceCaseViewer;
import jack.util.Logger;

import java.io.IOException;

import jpov.JpoFile;
import jpov.structure.Goal;
import jpov.structure.LemmaHierarchy;
import jpov.viewer.lemma.LemmaView;
import jpov.viewer.source.Box;
import jpov.viewer.source.SourceView;
import jpov.viewer.tree.TreeView;

import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.ScrolledComposite;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

/**
 * This class implements the lemma viewer
 * @author L. Burdy, A. Requet
 **/
public class JpovViewer
	implements ICaseExplorer, ILemmaViewer, ISourceCaseViewer {

	/**
	 * Image corresponding to the checked icon.
	 **/
	public static Image CHECKED;

	/**
	 * Image corresponding to the proved icon.
	 **/
	public static Image PROVED;

	/**
	 * Image corresponding to the unproved icon.
	 **/
	public static Image UNPROVED;

	/**
	 * Image corresponding to the prove icon.
	 **/
	protected static Image PROVE;

	/**
	 * Image corresponding to the save icon.
	 **/
	protected static Image SAVE;

	/**
	 * Image corresponding to the online icon.
	 **/
	protected static Image ONLINE;

	/**
	 * Image corresponding to the offline icon.
	 **/
	protected static Image OFFLINE;

	/**
	 * Image corresponding to the filter icon.
	 **/
	public static Image FILTER;

	/**
	 * Image corresponding to the printer icon.
	 **/
	public static Image PRINTER;

	/**
	 * Image corresponding to the invariant icon.
	 **/
	public static Image INVARIANT;

	/**
	 * Image corresponding to the local icon for hypothesis.
	 **/
	public static Image LOCALES;

	/**
	 * Image corresponding to the ensures icon.
	 **/
	public static Image ENSURES;

	/**
	 * Image corresponding to the exsures icon.
	 **/
	public static Image EXSURES;

	public static Image ASSERT;

	/**
	 * Image corresponding to the requires icon.
	 **/
	public static Image REQUIRES;

	/**
	 * Image corresponding to the loop invariant icon.
	 **/
	public static Image LOOP_INVARIANT;

	/**
	 * Image corresponding to the loop exsures icon.
	 **/
	public static Image LOOP_EXSURES;

	/**
	 * The number of image giving the informations concerning the proof rate of 
	 * a node
	 **/
	public static final int PROVED_IMAGES_COUNT = 3;

	/**
	 * The array containing the images that give informations concerning the 
	 * proof rate of a node
	 */
	public static Image provedImages[];

	/**
	 * The current display
	 **/
	protected static Display display;

	/**
	 * Returns the current display.
	 * @return <code>display</code>
	 **/
	public static Display getDisplay() {
		return display;
	}

	/**
	 * The currently visualized jpo file
	 **/
	protected JpoFile pov;

	/** 
	 * Container that contains the content of the window. 
	 **/
	private SashForm sform;

	/**
	 * The currently selected goal
	 **/
	private Goal selectedGoal;

	/**
	 * The part of the view corresponding to the tree
	 **/
	protected TreeView treeView;

	/**
	 * The part of the view corresponding to the source
	 **/
	private SourceView sourceView;

	/**
	 * The part of the view corresponding to the lemma viewers
	 **/
	private LemmaView lemmaView;

//	/**
//	 * Return the selection corresponding to the currently selected hypothesis.
//	 * <p>
//	 * As several hypothesis windows can be used, the chosen selection
//	 * correspond to the first selection that is not empty.
//	 * 
//	 * @return null if no selection has been found, the selection 
//	 *    otherwise.
//	 */
//	public Object[] getHypSelection() {
//		return lemmaView.getHypSelection();
//	}

//	/**
//	 * Return an enumeration enumerating the different hypothesis 
//	 * viewers.
//	 * <p>
//	 * All the elements returned by this enumeration will be of type
//	 * <code>TableViewer</code>.
//	 */
//	public Enumeration getHypViewers() {
//		return lemmaView.getHypViewers();
//	}

	/**
	 * Sets the goal to be displayed in the lemma views
	 * @param g The goal to display
	 **/
	public void setGoalText(Goal g) {
		lemmaView.setGoalText(g, false);
	}

	/**
	 * Sets the lemma to be displayed in the lemma views
	 * @param l The lemma from whitch hypotheses have to be displayed
	 **/
	public void setHypText(jpov.structure.Lemma l) {
		lemmaView.setHypText(l);
	}

	public void setHypText(LemmaHierarchy l) {
		lemmaView.setHypText(l);
	}

	/**
	 * Disposes the view
	 **/
	protected void dispose() {
		sform.dispose();
	}

	/** 
	 * Returns the Shell containing the JpovViewer.
	 */
	public Shell getShell() {
		return sform.getShell();
	}

//	/**
//	 * Sets the status of the JML file lemma getting informations into a loaded
//	 * pmi file and update the view
//	 * @param pmiTree the {@link AST} corresponding to the pmi file
//	 **/
//	public void setStatus(AST pmiTree) {
//		pov.setStatus(pmiTree);
//		displayStatus();
//	}

	/**
	 * Updates the view
	 **/
	public void displayStatus() {
		treeView.updateLeftComp(pov);
	}

	/**
	 * Returns <code>this</code>
	 **/
	protected JpovViewer getThis() {
		return this;
	}

//	/** 
//	 * Create the content of the widget and adds it within the given composite
//	 * widget.
//	 * @param config The current configuration
//	 * @param ab The current Atelier B server
//	 * @param parent The parent composite
//	 **/
//	//@ requires config != null;
//	//@ ensures sform != null;
//	public void createContent(
//		IJml2bConfiguration config,
//		AbServer ab,
//		Composite parent) {
//		// the SashForm is the form that contains the separator
//		sform = new SashForm(parent, SWT.HORIZONTAL);
//
//		treeView = new TreeView(sform, pov, this);
//
//		ViewForm right_pane = new ViewForm(sform, SWT.NONE);
//
//		int[] sform_weights = { 1, 4 };
//		sform.setWeights(sform_weights);
//
//		// create a sashform for resizing source/goal-bview, and add it to
//		// the right pane
//		SashForm right_sform = new SashForm(right_pane, SWT.VERTICAL);
//		right_pane.setContent(right_sform);
//
//		sourceView =
//			new SourceView(
//				right_sform,
//				pov,
//				treeView,
//				this,
//				ab,
//				config.getViewerFont());
//
//		lemmaView = new LemmaView(config, right_sform);
//
//		int right_sform_weights[] = { 3, 1 };
//		right_sform.setWeights(right_sform_weights);
//
//	}

//	/**
//	 * Updates the content of the viewer
//	 * @param ab The current Atelier B server
//	 **/
//	protected void updateContent(AbServer ab) {
//		if (pov != null) {
//			// case where a pov has been added
//			treeView.updateLeftComp(pov);
//			sourceView.updateContent(pov, this, ab);
//			lemmaView.erase();
//		} else {
//			// no pov. resets the corresponding controls so that they appears
//			// empty
//			treeView.eraseInput();
//			sourceView.erase();
//			// sets the content of the viewers to empty
//			lemmaView.erase();
//		}
//	}

//	/**
//	 * Updates the content of the viewer
//	 * @param p The currently viewed jpo file
//	 * @param ab The current Atelier B server
//	 **/
//	public void updateContent(JpoFile p, AbServer ab) {
//		this.pov = p;
//		updateContent(ab);
//	}

	/**
	 * Returns the selectedGoal.
	 * @return Goal
	 */
	public Goal getSelectedGoal() {
		return selectedGoal;
	}

	/**
	 * Sets the selectedGoal.
	 * @param selectedGoal The selectedGoal to set
	 */
	public void setSelectedGoal(Goal selectedGoal) {
		this.selectedGoal = selectedGoal;
	}

	public void setTopIndex(int line) {
		StyledText st = getSourceView().getSourceText();
		if (line >= 0)
			((ScrolledComposite) st.getParent()).setOrigin(
				st.getLocationAtOffset(st.getOffsetAtLine(line)));
	}

	public boolean highlight(Color fgcolor, Color bgcolor, int line, int column, int length) {
		StyledText text = getSourceView().getSourceText();
		int start = text.getOffsetAtLine(line) + column;
		StyleRange sr = text.getStyleRangeAtOffset(start);
		if (sr == null || sr.foreground == Box.GREEN) {
			StyleRange styleRange = new StyleRange();
			styleRange.start = start;
			styleRange.length = length;
			styleRange.fontStyle = SWT.BOLD;
			styleRange.foreground = fgcolor;
			styleRange.background = bgcolor;

			try {
				text.setStyleRange(styleRange);
				return true;
			} catch (Exception iae) {
				Logger.err.println(
					iae.toString()
						+ "Bad style range. start : "
						+ start
						+ "; length : "
						+ length
						+ "; getCharCount() : "
						+ text.getCharCount());
			}
		}
		return false;

	}

	public void eraseColor() {
		getSourceView().getSourceText().replaceStyleRanges(
			0,
			getSourceView().getSourceText().getText().length(),
			new StyleRange[0]);
	}

	/**
	 * Returns the part of the view corresponding to the tree
	 * @return <code>treeView</code>
	 **/
	public TreeView getLeftTree() {
		return treeView;
	}

	public TreeViewer getTree() {
		return treeView.getTree();
	}

	/**
	 * Returns the selected items
	 **/
	public Object[] getTreeSelection() {
		return ((StructuredSelection) treeView.getTree().getSelection())
			.toArray();
	}

	/**
	 * Returns the part of the view corresponding to the source
	 * @return <code>sourceView</code>
	 **/
	public SourceView getSourceView() {
		return sourceView;
	}

	public void save() throws IOException {
		pov.save();
	}

	public int getLayout() {
		return FLAT;
	}

	/* (non-Javadoc)
	 * @see jack.plugin.perspective.ICaseExplorer#setGoalMenu()
	 */
	public void setGoalMenu() {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see jack.plugin.perspective.ICaseExplorer#setLemmaMenu()
	 */
	public void setLemmaMenu() {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see jack.plugin.perspective.ICaseExplorer#setMultipleGoalMenu()
	 */
	public void setMultipleGoalMenu() {
		// TODO Auto-generated method stub
		
	}
}
