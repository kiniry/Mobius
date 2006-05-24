//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: TreeFilter.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.tree;

import jpov.structure.Class;
import jpov.structure.Goal;
import jpov.structure.JmlFile;
import jpov.structure.Lemma;
import jpov.structure.Method;
import jpov.structure.Proofs;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;

/**
 * This class implements a filter for tree. Jmlfile, classes, methods, 
 * lemmas and goals are displayed or not depending of the configuration 
 * choosen in the filter window.
 * @author L. Burdy
 **/
public class TreeFilter extends ViewerFilter {

    /**
     * The filter window allowing to edit the filter.
     **/
    TreeFilterWindow tfw;
    
    /**
     * Constructs a filter with an associated filter window
     * @param tfw The filter window
     */
    public TreeFilter(TreeFilterWindow tfw) {
        this.tfw = tfw;
    }

    /**
     * Selects the node tree to display
     * <UL>
     * <li> the jml file is always displayed
     * <li> a class is displayed if its proof percent reach the wished rank
     * <li> a method is displayed if its proof percent reach the wished rank
     * <li> a case is displayed if its proof percent reach the wished rank
     * <li> a goal is displayed if its proof status and its origin correspond
     * to displayed ones.
     * </UL>
     **/
	public boolean select(
		Viewer viewer,
		Object parentElement,
		Object element) {
		if (element instanceof JmlFile)
			return true;
		if (element instanceof Class)
			return ((Class) element).percentProved() <= tfw.getClassPercent();
		if (element instanceof Method)
			return ((Method) element).percentProved() <= tfw.getMethodPercent();
		if (element instanceof Proofs)
			return ((Proofs) element).percentProved() <= tfw.getMethodPercent();
		if (element instanceof Lemma)
			return ((Lemma) element).percentProved() <= tfw.getCasesPercent();
		if (element instanceof Goal)
			return (
				((((Goal) element).isProved() && tfw.isShowProved())
					|| (!((Goal) element).isProved() && tfw.isShowUnProved()))
					&& (!tfw.isShowGoalType()
						|| tfw.getShowTypes(((Goal) element).getGoalType())));
		return true;
	}

}
