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

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.ClassLoadException;
import jml2b.exceptions.Jml2bException;

/**
 * 
 * @author L. Burdy
 */
public abstract class JmlFileEntry {

	public abstract File getFile();

	public abstract String getName();

	public abstract String getAbsolutePath();

	/**
	 * @param defaultExternalFile
	 */
	public abstract void loadClass(IJml2bConfiguration config, boolean defaultExternalFile) throws ClassLoadException,
	Jml2bException;

	/** 
	 * Load the given Java/JML file and return a new JmlFile structure.
	 * Errors and warnings reported by the JML parser are stored in 
	 * the provided vectors, that contains jml.ErrorMessage.
	 */
//	public abstract JmlFile loadFile(boolean external, Vector error_vector, Vector warning_vector);

	//	public abstract InputStream getInputStream() throws IOException;

}