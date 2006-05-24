//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: TreeSorter.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.tree;

import jack.plugin.perspective.ICaseExplorer;
import jpov.structure.Goal;
import jpov.structure.Lemma;
import jpov.structure.Method;
import jpov.structure.StaticInitProofs;
import jpov.structure.WellDefInvProofs;
import jpov.structure.WellDefinedMethodProofs;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerSorter;

/**
 * This class implements a sorter for the node of the tree
 * @author L. Burdy
 **/
public class TreeSorter extends ViewerSorter {

	ICaseExplorer caseExp;

	public TreeSorter(ICaseExplorer explorer) {
		super();
		caseExp = explorer;
	}
	/**
	 * Compares two nodes. When the two nodes are lemmas, compares the 
	 * <code>caseNum</code>.
	 **/
	public int compare(Viewer viewer, Object e1, Object e2) {
		if (e1 instanceof WellDefInvProofs
			&& (e2 instanceof Method || e2 instanceof StaticInitProofs))
			return -1;
		if ((e1 instanceof Method || e1 instanceof StaticInitProofs)
			&& e2 instanceof WellDefInvProofs)
			return 1;

		if (e1 instanceof StaticInitProofs && e2 instanceof Method)
			return -1;
		if (e1 instanceof Method && e2 instanceof StaticInitProofs)
			return 1;

		if (e1 instanceof Method && e2 instanceof Method) {
			Method m1 = (Method) e1;
			Method m2 = (Method) e2;
			if (m1.isStatic() && !m2.isStatic())
				return -1;
			if (m2.isStatic() && !m1.isStatic())
				return 1;
			if (m1.isConstructor() && !m2.isConstructor())
				return -1;
			if (m2.isConstructor() && !m1.isConstructor())
				return 1;
			return super.compare(viewer, e1, e2);
		}

		if (e1 instanceof WellDefinedMethodProofs && e2 instanceof Lemma)
			return -1;
		if (e1 instanceof Lemma && e2 instanceof WellDefinedMethodProofs)
			return 1;

		if (caseExp.getLayout() == ICaseExplorer.FLAT
			&& e1 instanceof Lemma
			&& e2 instanceof Lemma) {
			return ((Lemma) e1).getNum() - ((Lemma) e2).getNum();
		}

		if (e1 instanceof Goal && e2 instanceof Goal)
			return ((Goal) e1).getNumber() - ((Goal) e2).getNumber();
		return super.compare(viewer, e1, e2);
	}

}
