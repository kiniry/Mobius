//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.util;

import java.util.Comparator;

/**
 * @author L. Burdy
 */
public class FileUpdateComparator implements Comparator {

	/* (non-Javadoc)
	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
	 */
	public int compare(Object o1, Object o2) {
		if (((FileUpdate) o1).getLine() < ((FileUpdate) o2).getLine())
			return -1;
		else
			return 1;
	}

}
