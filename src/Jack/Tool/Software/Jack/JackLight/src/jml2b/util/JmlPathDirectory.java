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
public class JmlPathDirectory extends JmlPathEntry {

	String dir;

	public JmlPathDirectory(String s) {
		dir = s;
	}

	public boolean checkDirectory(String dir_name) {
		File f = new File(dir + dir_name);
		if (f.exists() && f.isDirectory()) {
			return true;
		}
		return false;
	}

	public JmlFileEntry checkFile(File file) {
		File f = new File(dir, file.getPath());
		//Logger.get().println(f.toString() + " " + f.exists());
		if (f.exists()) {
			return new JmlEntryFile(f);
		}
		else {
			return null;
		}
	}

}
