//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: TreeItemSelection
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.tree;

import jack.plugin.perspective.ICaseExplorer;
import jack.plugin.perspective.ILemmaViewer;
import jack.plugin.perspective.ISourceCaseViewer;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import jpov.structure.Goal;
import jpov.structure.Lemma;
import jpov.structure.LemmaHierarchy;
import jpov.structure.Method;
import jpov.structure.VirtualFormula;
import jpov.viewer.source.Box;

import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;



/**
 * Tis class implements a selection changed listener for the tree.
 * @author L. Burdy
 */
public class TreeItemSelection implements ISelectionChangedListener {

	/**
	 * The current viewer
	 **/
	private ILemmaViewer ew;

	private ISourceCaseViewer sv;

	/**
	 * The currently displayed highlighted boxes set
	 **/
	private Vector labels = new Vector();

	private ICaseExplorer ce;

	List selectedGoals = new ArrayList();
	
	/*@
	  @ private invariant labels != null;
	  @ private invariant labels.elementType <: \type(Box);
	  @*/

	/**
	 * Constructs a selection changed listener
	 * @param ew The current viewer
	 **/
	public TreeItemSelection(ILemmaViewer ew, ISourceCaseViewer sv, ICaseExplorer ce) {
		this.ew = ew;
		this.sv = sv;
		labels = new Vector();
		this.ce = ce;
	}



	private void unhighlight() {
		labels = new Vector();
		sv.eraseColor();
	}

	/**
	 * Supress the currently highlighted boxes and highlights the boxes 
	 * corresponding to a lemma and adds them to the label set.
	 * @param l The lemma
	 **/
	private void highlightLemma(Lemma l) {
		unhighlight();
		for (int i = 0; i < l.getHyp().length; i++) {
			VirtualFormula vf = l.getHyp()[i];
			Enumeration e = vf.getFlow();
			while (e.hasMoreElements()) {
				Box b = (Box) e.nextElement();
				if (b.highlightBox(sv))
					labels.add(b);
			}
		}
		for (int i = 0; i < l.getFlow().length; i++) {
			if (l.getFlow()[i].highlightBox(sv))
				labels.add(l.getFlow()[i]);
		}
	}

	/**
	 * Supress the currently highlighted boxes and highlights the boxes 
	 * corresponding to a lemma and adds them to the label set.
	 * @param l The lemma
	 **/
	private void highlightLemma(LemmaHierarchy l) {
		unhighlight();
		Enumeration e1 = l.getHyp().elements();
		while (e1.hasMoreElements()) {
			VirtualFormula vf = (VirtualFormula) e1.nextElement();
			Enumeration e = vf.getFlow();
			while (e.hasMoreElements()) {
				Box b = (Box) e.nextElement();
				if (b.highlightBox(sv))
					labels.add(b);
			}
		}
		e1 = l.getFlow().elements();
		while (e1.hasMoreElements()) {
			Box element = (Box) e1.nextElement();
			if (element.highlightBox(sv))
				labels.add(element);
			
		}
	}

	/**
	 * Highlights the boxes corresponding to the goal and adds them to the
	 * label set.
	 * @param g The goal
	 **/
	private void highlightGoal(Goal g) {
		Enumeration e = g.getVf().getFlow();

		while (e.hasMoreElements()) {
			Box b = (Box) e.nextElement();
			if (b.highlightBox(sv))
				labels.add(b);
		}
	}

	/**
	 * Displays the hypothesis and the goal associated with a goal and its 
	 * associated lemma.
	 * @param l The lemma
	 * @param g The goal
	 **/
	private void editGoal(Lemma l, Goal g) {
		ew.setGoalText(g);
		ew.setHypText(l);
		ce.setGoalMenu();
	}

	/**
	 * Displays the hypothesis associated with a lemma
	 * @param l The lemma
	 **/
	private void editLemma(Lemma l) {
		ew.setHypText(l);
		ce.setLemmaMenu();
	}

	private void editLemma(LemmaHierarchy l) {
		ew.setHypText(l);
	}

	/**
	 * Sets the goal text to <code>null</code>.
	 **/
	private void resetGoal() {
		ew.setGoalText(null);
	}
	
	public List getSelectedGoals() {
		return selectedGoals;
	}
	public void resetSelectedGoals() {
		selectedGoals.clear();
	}
	/**
	 * If the selected item is a method, a lemma or a goal, sets the origin of 
	 * the text viewer to the first line of the selected method.
	 * If the selected item is a lemma, displays the hypothesis; highlights the
	 * corresponding boxes and reset the goals window.
	 * If the selected item is a goal, displays the hypothesis and the goal, 
	 * highlights the corresponding boxes.
	 * @param event The selection event
	 **/
	public void selectionChanged(SelectionChangedEvent event) {
		// if the selection is empty clear the label
//		if (sv instanceof JpovViewer)
//			 ((JpovViewer) sv).setSelectedGoal(null);
		ce.setLemmaMenu();
		if (event.getSelection().isEmpty()) {
			return;
		}

		if (event.getSelection() instanceof IStructuredSelection) {
			IStructuredSelection selection =
				(IStructuredSelection) event.getSelection();
			selectedGoals.clear();
			
			for (Iterator iterator = selection.iterator();
				iterator.hasNext();
				) {
				Object domain = iterator.next();
				int line = 0;
				if (domain instanceof Method) {
					unhighlight();
					resetGoal();
					//unselectGoals();
					line = ((Method) domain).getFirstLine() - 1;
				}
				if (domain instanceof LemmaHierarchy) {
					LemmaHierarchy l = (LemmaHierarchy) domain;
					highlightLemma(l);
					editLemma(l);
					resetGoal();
					//unselectGoals();
					if (l.getParent() instanceof Method) {
						line = ((Method) (l.getParent())).getFirstLine() - 1;
					}
				}
				if (domain instanceof Lemma) {
					Lemma l = (Lemma) domain;
					highlightLemma(l);
					editLemma(l);
					resetGoal();
					//unselectGoals();
					if (l.getParent() instanceof Method) {
						line = ((Method) (l.getParent())).getFirstLine() - 1;
					}
				} else if (domain instanceof Goal) {
					Goal g = (Goal) domain;
					Lemma l = (Lemma) g.getParent();
//					if (sv instanceof JpovViewer)
//						 ((JpovViewer) sv).setSelectedGoal(g);
					selectedGoals.add(g);
					highlightLemma(l);
					highlightGoal(g);
					
					editGoal(l, g);

					if (l.getParent() instanceof Method) {
						line = ((Method) (l.getParent())).getFirstLine() - 1;
					}
				}
				if (line >= 0)
					sv.setTopIndex(line);
			}
		}
		if(selectedGoals.size() > 1)
			ce.setMultipleGoalMenu();
	}

	/**
	 * Returns the set of labels
	 * @return the set of currently displayed highlighted boxes.
	 **/
	public Enumeration getLabels() {
		return labels.elements();
	}

}
