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
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.io.Serializable;

/**
 *
 *  @author L. Burdy
 **/
public class JmlEntryFile extends JmlSourceEntryFile implements Serializable {

	static final long serialVersionUID = -3266071808733837898L;
	
	transient File f;
	String absolutePath;

	public JmlEntryFile(File f) {
		this.f = f;
		absolutePath = f.getAbsolutePath();
	}

  public File getFile() {
		return f;
	}

	public InputStream getInputStream() throws FileNotFoundException {
		return new FileInputStream(f);
	}

	public String getName() {
		return f.getName();
	}

	public String getAbsolutePath() {
		return absolutePath;
	}

	public String toString() {
		return f.toString();
	}

}
