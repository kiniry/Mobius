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

import org.eclipse.compare.IStreamContentAccessor;
import org.eclipse.core.runtime.CoreException;

/**
 *
 *  @author L. Burdy
 **/
public class JmlFileStream implements IStreamContentAccessor {

	private File jf;

	public JmlFileStream(File jf) {
		this.jf = jf;
	}

	public InputStream getContents() throws CoreException {
		try {
			return new FileInputStream(jf);
		} catch (FileNotFoundException fnfe) {
			return null;
		}
	}

}

