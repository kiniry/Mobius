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
 *
 *  @author L. Burdy
 **/
public class UpdatedJmlFile {
	File oldF;
	File newF;

	UpdatedJmlFile(File jf, File n) {
		this.oldF = jf;
		this.newF = n;
	}
	/**
	 * @return
	 */
	public File getJf() {
		return oldF;
	}

	/**
	 * @return
	 */
	public File getNewF() {
		return newF;
	}

}
