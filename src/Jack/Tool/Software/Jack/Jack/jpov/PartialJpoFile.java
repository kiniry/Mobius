//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JpoFile
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov;

import jack.plugin.JackPlugin;
import jack.plugin.JpovUtil;
import jack.plugin.edit.EditedFile;

import java.io.BufferedInputStream;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.RandomAccessFile;

import jml2b.IJml2bConfiguration;
import jml2b.util.JpoInputStream;
import jpov.structure.PartialJmlFile;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;

/**
 * This class defines a JPO file. That corresponds to a file and its associated
 * informations stored into a JML file structure.
 * @author L. Burdy
 **/
public class PartialJpoFile {

	public static PartialJpoFile getJpo(ICompilationUnit c) {
		IFile jpo_file = JackPlugin.getJpoFile(c);
		if (jpo_file != null) {
			try {
				return JpovUtil.loadPartialJpoFile(new EditedFile(jpo_file));
			} catch (Exception e) {
				;
			}
		}
		return null;
	}

	/**
	 * The jml file associated with this JPO file
	 **/
	private PartialJmlFile jmlfile;

	private String name;

	/*@
	  @ private invariant jmlfile != null;
	  @*/

	/**
	 * Constucts a JPO file from a given repository and a given name. Loads the 
	 * file and store the informations into a JML file structure.
	 * @param dir The repository
	 * @param name The file name
	 **/
	/*@
	  @ requires dir != null && name != null;
	  @*/
	public PartialJpoFile(IJml2bConfiguration config, String name)
		throws IOException, jml2b.exceptions.LoadException {
		FileInputStream istrp =
			new FileInputStream(
				new File(config.getSubdirectory(), name + ".jpop"));
		DataInputStream ostrp =
			new DataInputStream(new BufferedInputStream(istrp));
		File istr = new File(config.getSubdirectory(), name + ".jpo");
		RandomAccessFile raf = new RandomAccessFile(istr, "r");
		JpoInputStream ostr = new JpoInputStream(raf, ostrp);
		// read packages
		this.name = name;
		jmlfile = new PartialJmlFile(ostr);

		raf.close();
		ostrp.close();
		istrp.close();
	}

	/**
	 * Returns the associated JML file
	 * @return <code>jmlfile</code>
	 **/
	public PartialJmlFile getPartialJmlFile() {
		return jmlfile;
	}

	/**
	 * @return
	 */
	public String getName() {
		return name;
	}

}