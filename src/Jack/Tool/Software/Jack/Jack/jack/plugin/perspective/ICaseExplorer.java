//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jack.plugin.perspective;

import java.io.IOException;

import org.eclipse.jface.viewers.TreeViewer;

/**
 * This interface defines a case explorer.
 * 
 * @author L. Burdy
 **/
public interface ICaseExplorer {

	/**
	 * Layout corresponding to a flat presentation of the cases.
	 */
	static final int FLAT = 0;
	
	/**
	 * Layout corresponding to a hierarchical presentation of the cases.
	 */
	static final int HIERARCHY = 1;

	public void displayStatus();

	public TreeViewer getTree();

	public Object[] getTreeSelection();

	public void save() throws IOException;

	/**
	 * Returns the current layout
	 * @return FLAT or HIERARCHY
	 */
	public int getLayout();

	/**
	 * 
	 */
	public void setGoalMenu();

	/**
	 * 
	 */
	public void setLemmaMenu();

	/**
	 * 
	 */
	public void setMultipleGoalMenu();

}
