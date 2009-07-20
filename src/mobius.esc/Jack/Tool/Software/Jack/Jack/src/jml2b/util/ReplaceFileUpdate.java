//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.util;

import java.io.File;

/**
 * @author L. Burdy
 */
public class ReplaceFileUpdate extends FileUpdate {

	int begin;

	public ReplaceFileUpdate(File f, String s, int b) {
		super(f, s);
		begin = b;
	}
	
	public int getLine() {
		return begin;
	}

}
