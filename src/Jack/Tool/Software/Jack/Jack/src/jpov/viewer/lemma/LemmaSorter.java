//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: LemmaSorter.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.lemma;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerSorter;

/**
 * The class implements a sorter for the hypothesis viewer
 * @author L. Burdy
 **/
public class LemmaSorter extends ViewerSorter {

	/**
	 * The associated filter window
	 **/
	private LemmaFilterWindow lfw;

	/**
	 * Constructs a lemma filter
	 * @param lfw The associated filter window
	 **/
	public LemmaSorter(LemmaFilterWindow lfw) {
		this.lfw = lfw;
	}

    /**
     * If the two lines have the same origin, compare their nums, otherwise 
     * compare their origins.
     */
    /*@
      @ requires \typeof(e1) <: \type(HypLine) && \typeof(e2) <: \type(HypLine);
      @*/
	public int compare(Viewer viewer, Object e1, Object e2) {
		HypLine h1 = (HypLine) e1;
		HypLine h2 = (HypLine) e2;
		if (lfw.isShow(h1) != lfw.isShow(h2))
			return lfw.isShow(h1) - lfw.isShow(h2);
//		else if (h1.getOrigin() != h2.getOrigin())
//			return h1.getOrigin() - h2.getOrigin();
		else
			return h1.getNum() - h2.getNum();
	}

}
