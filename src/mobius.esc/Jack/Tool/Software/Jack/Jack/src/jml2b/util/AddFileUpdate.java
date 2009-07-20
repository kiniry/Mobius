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
public class AddFileUpdate extends FileUpdate {

	int line;

	public AddFileUpdate(File f, int l, String s) {
		super(f, s);
		line = l;
	}

	public int getLine() {
		return line;
	}
}
