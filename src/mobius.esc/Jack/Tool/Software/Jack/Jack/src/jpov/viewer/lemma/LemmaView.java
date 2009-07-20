//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: LemmaViewer.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.lemma;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.LanguageException;
import jml2b.languages.Languages;
import jpov.structure.Class;
import jpov.structure.Goal;
import jpov.structure.LemmaHierarchy;
import jpov.structure.Method;
import jpov.structure.TreeObject;

import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.ViewForm;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;

/**
 * This class implements the part of the viewer that displays the lemmas in 
 * different languages.
 * @author L. Burdy, A. Requet
 **/
public class LemmaView {

	/**
	 * Vector of TableViewer elements that contains the different 
	 * goal viewers.
	 */
	private Hashtable goalViewers;

	/**
	 * Vector of TableViewer elements that contains the different 
	 * goal viewers.
	 */
	private Hashtable hypViewers;

	private LemmaFilterWindow lfw;

	private CTabFolder lemmaFold;

	private CTabItem selectedTab = null;

	private Vector tabItems;

	private jpov.structure.Lemma displayedLemma;
	private Goal displayedGoal;
	private LemmaHierarchy displayedLemmaHierachry;

	/*@
	  @ private invariant goalViewers != null
	  @                && hypViewers != null
	  @                && goalViewers.elementType <: \type(TableViewer)
	  @                && hypViewers.elementType <: \type(TableViewer)
	  @                && goalViewers.size() == hypViewers.size();
	  @*/

	/**
	 * Constructs the part of the view that displays the lemma
	 * @param config The current configuration
	 * @param right_sform The form corresponding to the right part of the view
	 **/
	public LemmaView(
		IJml2bConfiguration config,
		Composite right_sform,
		boolean horizontal) {
		// create the lemma notebook
		ViewForm lemma_pane = new ViewForm(right_sform, SWT.BAR);

		hypViewers = new Hashtable();
		goalViewers = new Hashtable();
		lfw = new LemmaFilterWindow(new Shell(), hypViewers);

		lemmaFold = new CTabFolder(lemma_pane, SWT.BOTTOM);

		tabItems = new Vector();

		Enumeration e = Languages.getLanguagesNames();
		while (e.hasMoreElements()) {
			String name = (String) e.nextElement();
			try {
				if (config.isViewShown(name)) {
					addLemmaViewer(
						name,
						new GoalContentProvider(
							Languages.getLanguageClass(name)),
						new HypContentProvider(name),
						horizontal);
				}
			} catch (LanguageException le) {
				;
			}

		}

		if (selectedTab != null)
			lemmaFold.setSelection(selectedTab);
		else {
			lemmaFold.setSelection(0);
			selectedTab = lemmaFold.getItem(0);
		}

		lemmaFold.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {
			}
			public void widgetSelected(SelectionEvent e) {
				CTabItem newTi = (CTabItem) e.item;
				if (selectedTab != null && !selectedTab.isDisposed()) {
					TableViewer tv =
						(TableViewer) hypViewers.get(selectedTab.getText());
					if (tv != null) {
						int i = tv.getTable().getSelectionIndex();
						tv = (TableViewer) hypViewers.get(newTi.getText());
						Object o = tv.getElementAt(i);
						if (o != null)
							tv.setSelection(new StructuredSelection(o), true);
					}
				}
				selectedTab = newTi;
			}

		});

		lemma_pane.setContent(lemmaFold);

	}

	public void redraw(
		IJml2bConfiguration config,
		boolean horizontal,
		boolean applySubstitution) {
		hypViewers.clear();
		goalViewers.clear();
		Enumeration e = tabItems.elements();
		while (e.hasMoreElements()) {
			CTabItem element = (CTabItem) e.nextElement();
			element.dispose();
			element = null;
		}
		tabItems = new Vector();
		e = Languages.getLanguagesNames();
		while (e.hasMoreElements()) {
			String name = (String) e.nextElement();
			try {
				if (config.isViewShown(name)) {
					addLemmaViewer(
						name,
						new GoalContentProvider(
							Languages.getLanguageClass(name)),
						new HypContentProvider(name),
						horizontal);
				}
			} catch (LanguageException le) {
				;
			}

		}
		lemmaFold.setSelection(0);
		selectedTab = lemmaFold.getItem(0);

		setGoalText(displayedGoal, applySubstitution);
		if (displayedLemma != null)
			setHypText(displayedLemma);
		else if (displayedLemmaHierachry != null)
			setHypText(displayedLemmaHierachry);

		lemmaFold.redraw();
	}

	/**
	 * Add a lemma viewer corresponding to a language
	 * @param lemma_fold The current folder where the viewer is added
	 * @param filter The current lemma filter
	 * @param language_name The language name to be displayed in the header of
	 * the viewer
	 * @param goal The associated goal content provider
	 * @param hyp The associated hypothesis content provider
	 */
	private void addLemmaViewer(
		String language_name,
		GoalContentProvider goal,
		HypContentProvider hyp,
		boolean horizontal) {

		CTabItem ti;
		ti = new CTabItem(lemmaFold, 0);
		ti.setText(language_name);

		SashForm sh =
			new SashForm(lemmaFold, horizontal ? SWT.HORIZONTAL : SWT.VERTICAL);
		ti.setControl(sh);

		tabItems.add(ti);

		TableViewer goal_viewer, hyp_viewer;
		hyp_viewer = new TableViewer(sh);
		hyp_viewer.setContentProvider(hyp);
		hyp_viewer.setLabelProvider(new MyLabelProvider());
		hyp_viewer.setInput(null);
		hyp_viewer.setSorter(new LemmaSorter(lfw));

		goal_viewer = new TableViewer(sh);
		goal_viewer.setContentProvider(goal);
		goal_viewer.setLabelProvider(new MyLabelProvider());
		goal_viewer.setInput(null);

		// add the viewers to the vectors
		goalViewers.put(language_name, goal_viewer);
		hypViewers.put(language_name, hyp_viewer);
	}

	public LemmaFilterWindow getLemmaFilterWindow() {
		return lfw;
	}

	/**
	 * Return the selection corresponding to the currently selected hypothesis.
	 * <p>
	 * As several hypothesis windows can be used, the chosen selection
	 * correspond to the first selection that is not empty.
	 * 
	 * @return null if no selection has been found, the selection 
	 *    otherwise.
	 */
	public Object[] getHypSelection() {
		Enumeration e = hypViewers.elements();
		while (e.hasMoreElements()) {
			TableViewer t = (TableViewer) e.nextElement();
			StructuredSelection sel = (StructuredSelection) t.getSelection();
			Object[] result = sel.toArray();
			if (result.length != 0) {
				return result;
			}
		}
		return null;
	}

	public TableViewer getSelectedTable() {
		Control[] ca =
			((SashForm) lemmaFold.getSelection().getControl()).getChildren();
		Enumeration e = hypViewers.elements();
		while (e.hasMoreElements()) {
			TableViewer element = (TableViewer) e.nextElement();
			if (element.getTable().isFocusControl()
				&& element.getControl() == ca[0]
				|| element.getControl() == ca[1])
				return element;
		}
		e = goalViewers.elements();
		while (e.hasMoreElements()) {
			TableViewer element = (TableViewer) e.nextElement();
			if (element.getTable().isFocusControl()
				&& element.getControl() == ca[0]
				|| element.getControl() == ca[1])
				return element;
		}
		return null;
	}

	/**
	 * Return an enumeration enumerating the different hypothesis 
	 * viewers.
	 * <p>
	 * All the elements returned by this enumeration will be of type
	 * <code>TableViewer</code>.
	 */
	public Enumeration getHypViewers() {
		return hypViewers.elements();
	}

	/**
	 * Sets the text to be displayed in the goal views
	 * @param g The goal to display
	 */
	public void setGoalText(Goal g, boolean applySubstitution) {
		displayedGoal = g;
		Enumeration e = goalViewers.elements();
		while (e.hasMoreElements()) {
			TableViewer t = (TableViewer) e.nextElement();
			(
				(GoalContentProvider) t
					.getContentProvider())
					.setApplySubstitution(
				applySubstitution);
			t.setInput(g);
		}
	}

	/**
	 * Sets the text to be displayed in the hypothesis views
	 * @param l The lemma fro whitch hypotheses havze to be displayed
	 */
	public void setHypText(jpov.structure.Lemma l) {
		displayedLemma = l;
		displayedLemmaHierachry = null;
		Enumeration e = hypViewers.elements();
		while (e.hasMoreElements()) {
			TableViewer t = (TableViewer) e.nextElement();
			t.setInput(l);
		}
		TreeObject p = (TreeObject) l.getParent();
		if (p instanceof Method)
			p = (TreeObject) p.getParent();
		lfw.setCurrentClass((Class) p);
	}

	public void setHypText(LemmaHierarchy l) {
		displayedLemma = null;
		displayedLemmaHierachry = l;
		Enumeration e = hypViewers.elements();
		while (e.hasMoreElements()) {
			TableViewer t = (TableViewer) e.nextElement();
			t.setInput(l);
		}
		TreeObject p = (TreeObject) l.getParent();
		if (p instanceof Method)
			p = (TreeObject) p.getParent();
		lfw.setCurrentClass((Class) p);
	}

	/**
	 * Sets the input of the viewers to <code>null</code>
	 **/
	public void erase() {
		displayedGoal = null;
		Enumeration e = goalViewers.elements();
		while (e.hasMoreElements()) {
			TableViewer t = (TableViewer) e.nextElement();
			t.setInput(null);
		}

		displayedLemma = null;
		displayedLemmaHierachry = null;
		e = hypViewers.elements();
		while (e.hasMoreElements()) {
			TableViewer t = (TableViewer) e.nextElement();
			t.setInput(null);
		}
	}
}
