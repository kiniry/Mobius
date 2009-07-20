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
import java.io.IOException;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

/**
 *
 *  @author L. Burdy
 **/
public class JmlPathJar extends JmlPathEntry {

	String jarFile;

	public JmlPathJar(String s) {
		jarFile = s;
	}

	public boolean checkDirectory(String dir_name) {
		try {
			ZipFile jf = new ZipFile(jarFile);
			try {
				ZipEntry ze = jf.getEntry(dir_name);
				if (ze != null && ze.isDirectory()) {
					return true;
				}
				return false;
			} finally {
				jf.close();
			}
		} catch (IOException ioe) {
			return false;
		}
	}

	public JmlFileEntry checkFile(File file) {
		try {
			ZipFile jf = new ZipFile(jarFile);
			try {
				ZipEntry ze = jf.getEntry(file.getPath());
				if (ze != null) {
					if (file.getAbsolutePath().indexOf(".class") == -1)
					return new JmlEntryFileInJar(jarFile, file.getPath());
					else
						return new JmlClassEntryFile(jarFile, file.getPath());
				}
				return null;
			} finally {
				jf.close();
			}
		} catch (IOException ioe) {
			return null;
		}
	}

}
