//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jack.plugin.edit;

import org.eclipse.swt.graphics.Color;

/**
 * Colored part of the edited java source.
 * 
 * @author L. Burdy
 **/
public class Box {

	/**
	 * The foreground color of the text.
	 **/
	Color fgcolor;
	
	/**
	 * The background color of the text.
	 **/
	Color bgcolor;
	
	/**
	 * The offset of the text.
	 **/
	int offset;
	
	/**
	 * The length of the text
	 **/
	int length;

	/**
	 * Creates a box
	 * @param fgc The foreground color
	 * @param bgc The background color
	 * @param o The offset
	 * @param le The length
	 **/
	Box(Color fgc, Color bgc, int o, int le) {
		fgcolor = fgc;
		bgcolor = bgc;
		offset = o;
		length = le;
	}

	/**
	 * Tests whether an offset belongs to the current box.
	 * @param o The tested offset
	 * @return true if the offset is in the box
	 **/
	boolean in(int o) {
		return (offset <= o && o < offset + length);
	}
	
	
	/**
	 * @return The background color.
	 **/
	public Color getBgcolor() {
		return bgcolor;
	}

	/**
	 * @return The foreground color.
	 **/
	public Color getFgcolor() {
		return fgcolor;
	}

}
