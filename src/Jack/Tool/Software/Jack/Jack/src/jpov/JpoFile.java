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

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.RandomAccessFile;

import jml2b.IJml2bConfiguration;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;
import jpov.structure.JmlFile;

/**
 * This class defines a JPO file. That corresponds to a file and its associated
 * informations stored into a JML file structure.
 * @author L. Burdy
 **/
public class JpoFile {

	static JmlFile loadedJmlFile;

	/**
	 * Loads a JPO file
	 * @param dir The repository where the file is located
	 * @param name The name of the file without the .jpo extension
	 * @return the constructed JML file structure.
	 **/
	/*@
	  @ ensures \result != null;
	  @*/
	public static JmlFile loadJmlFile(
		IJml2bConfiguration configuration,
		String name)
		throws IOException, jml2b.exceptions.LoadException {
		FileInputStream istrp =
			new FileInputStream(
				new File(configuration.getSubdirectory(), name + ".jpop"));
		DataInputStream ostrp =
			new DataInputStream(new BufferedInputStream(istrp));
		File istr = new File(configuration.getSubdirectory(), name + ".jpo");
		RandomAccessFile raf = new RandomAccessFile(istr, "r");
		JpoInputStream ostr = new JpoInputStream(raf, ostrp);

		if (loadedJmlFile != null)
			loadedJmlFile.freeLemmas();
		// read packages
		JmlFile jmlfile = JmlFile.loadJmlFile(configuration, istr, ostr);
		loadedJmlFile = jmlfile;

		raf.close();
		ostrp.close();
		return jmlfile;
	}

	/**
	 * The name of the JPO file
	 **/
	private String mchName;

	/**
	 * The jml file associated with this JPO file
	 **/
	private JmlFile jmlfile;

	/**
	 * The repository where is stored the JPO file.
	 **/
	private File directory;

	private RandomAccessFile raf;

	private IJml2bConfiguration config;

	/*@
	  @ private invariant mchName != null
	  @                && jmlfile != null
	  @                && directory != null;
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
	public JpoFile(IJml2bConfiguration config, String name)
		throws IOException, jml2b.exceptions.LoadException {
		mchName = name;
		directory = config.getSubdirectory();
		FileInputStream istrp =
			new FileInputStream(
				new File(config.getSubdirectory(), name + ".jpop"));
		DataInputStream ostrp =
			new DataInputStream(new BufferedInputStream(istrp));
		File istr = new File(config.getSubdirectory(), name + ".jpo");
		raf = new RandomAccessFile(istr, "r");
		JpoInputStream ostr = new JpoInputStream(raf, ostrp);

		if (loadedJmlFile != null)
			loadedJmlFile.freeLemmas();

		// read packages
		jmlfile = JmlFile.loadJmlFile(config, istr, ostr);
		this.config = config;
		loadedJmlFile = jmlfile;

		// The file is closed in the finalize method.
		//		raf.close();
		ostrp.close();
	}

	/**
	 * Saves the file into a
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a> and save
	 * the proof status into a .pmi file.
	 * @throws IOException
	 **/
	public void save() throws IOException {
		File f = new File(directory, mchName + ".jpo");
		// open the file
		JpoOutputStream stream =
			new JpoOutputStream(
				new BufferedOutputStream(new FileOutputStream(f)));
		jmlfile.save(config, stream);
		stream.close();

		File fp = new File(directory, mchName + ".jpop");
		// open the file
		DataOutputStream streamp =
			new DataOutputStream(
				new BufferedOutputStream(new FileOutputStream(fp)));
		stream.save(streamp);
		streamp.close();
	}

	/**
	 * Sets all the lemma to unprove
	 **/
	public void unprove() {
		jmlfile.unprove();
	}

	/**
	 * Returns the number of proof obligations.
	 * @return the number of proof obligations
	 */
	public int getNumPos() {
		return jmlfile.getNbPo();
	}

	/**
	 * Returns the JPO file name with the extension
	 * @return the JPO file name with the extension
	 **/
	public String getJpoName() {
		return mchName + ".jpo";
	}

	/**
	 * Returns the JPO file name
	 * @return <code>mchName</code>
	 **/
	public String getName() {
		return mchName;
	}

	/**
	 * Returns the associated JML file
	 * @return <code>jmlfile</code>
	 **/
	public JmlFile getJmlFile() {
		return jmlfile;
	}

	/**
	 * Returns the repository
	 * @return <code>directory</code>
	 **/
	public File getDirectory() {
		return directory;
	}

	protected void finalize() throws Throwable {
		super.finalize();
		if (raf != null)
			raf.close();
	}

	public void close() throws IOException {
		if (raf != null)
			raf.close();
	}

	/**
	 * 
	 */
	public void finalizeLoad() {
		jmlfile.finalizeLoad();
	}

}