//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jack.plugin.perspective;

import jpov.structure.Goal;
import jpov.structure.LemmaHierarchy;

/**
 * This interface defines a lemma viewer.
 * 
 * @author L. Burdy
 **/
public interface ILemmaViewer {

	/**
	 * Set the goal to display in the goal part of the view
	 * @param g The goal to display.
	 */
	public void setGoalText(Goal g);

	/**
	 * Sets the hypotheses to be displayed in the lemma views
	 * @param l The lemma from whitch hypotheses have to be displayed
	 **/
	public void setHypText(jpov.structure.Lemma l);
	
	/**
	 * Sets the hypotheses to be displayed in the lemma views
	 * @param l The lemma hierarchy containing some hypotheses to be displayed
	 */
	public void setHypText(LemmaHierarchy l);

}
