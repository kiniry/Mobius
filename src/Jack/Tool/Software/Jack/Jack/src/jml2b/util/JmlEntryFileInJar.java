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
import java.io.InputStream;
import java.io.Serializable;
import java.util.zip.ZipFile;

/**
 *
 *  @author L. Burdy
 **/
public class JmlEntryFileInJar extends JmlSourceEntryFile implements Serializable {

	static final long serialVersionUID = 9045845756306025043L;	
	
	String ze;
	String zf;

	public JmlEntryFileInJar(String zf, String ze) {
		this.ze = ze;
		this.zf = zf;
	}

	public File getFile() {
		return new File(zf + File.separator + ze);
	}

	public InputStream getInputStream() throws IOException {
		ZipFile lzf = new ZipFile(zf);
		return lzf.getInputStream(lzf.getEntry(ze));
	}

	public String getName() {
		return ze;
	}

	public String getAbsolutePath() {
		return zf + ":" + ze;
	}

	public String toString() {
		return ze + " in " + zf;
	}

}
