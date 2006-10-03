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
public abstract class JmlPathEntry {

	public static JmlPathEntry[] factory(String[] path) {
		JmlPathEntry[] res = new JmlPathEntry[path.length];
		for (int i=0; i < path.length; i++)
		if (new File(path[i]).isDirectory())
			res[i] = new JmlPathDirectory(path[i]);
		else 
			res[i] = new JmlPathJar(path[i]);	
		return res;
	}

	public abstract JmlFileEntry checkFile(File file);
	
	public abstract boolean checkDirectory(String dir_name);

}
