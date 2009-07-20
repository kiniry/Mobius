//******************************************************************************
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jack.plugin.perspective;

import org.eclipse.swt.graphics.Color;

/**
 * This interface defines a source viewer.
 * 
 * @author L. Burdy
 **/
public interface ISourceCaseViewer {

	void setTopIndex(int line);

	boolean highlight(
		Color fgcolor,
		Color bgcolor,
		int line,
		int column,
		int length);

	void eraseColor();

}
