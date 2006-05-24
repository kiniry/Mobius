//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JmlFile
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.structure;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.LoadException;
import jml2b.languages.Languages;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;

/**
 * This class implements the root node of the tree.
 * @author L. Burdy
 **/
public class JmlFile extends TreeObject implements IJmlFile {

	/**
	 * Loads the root node from a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The input stream corresponding to the JPO file
	 * @return The constructed root node.
	 * @throws LoadException when the file format is not correct.
	 **/
	public static JmlFile loadJmlFile(
		IJml2bConfiguration config,
		File jpoFile,
		JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		int ff;
		if ((ff = s.readInt())
			!= jml2b.structure.java.JmlFile.JPO_FILE_FORMAT_VERSION)
			throw new jml2b.exceptions.LoadException("Wrong file format." + ff);
		String filename = s.readUTF();
		int nbPo = s.readInt(); // Po 
		int nbPoProved = s.readInt(); // PoProved
		int nbLang = s.readInt(); // nbLanguages
		if (nbLang != Languages.getNbLanguages())
			throw new LoadException("Wrong file format");
		String[] langNames = new String[nbLang];
		boolean[] langGenerated = new boolean[nbLang];
		for (int i = 0; i < nbLang; i++) {
			langNames[i] = s.readUTF();
			langGenerated[i] = s.readBoolean();
			config.setFileGenerated(langNames[i], langGenerated[i]);
			if (Languages.getIndex(langNames[i]) != i)
				throw new LoadException("Wrong file format");
			s.readInt(); // nbPoProved
		}
		JmlFile jf = new JmlFile(filename, jpoFile, langNames, langGenerated);
		int size = s.readInt();
		String[] depends = new String[size];
		for (int j = 0; j < size; j++)
			depends[j] = s.readUTF();
		Class[] classes = new Class[s.readInt()];
		for (int j = 0; j < classes.length; j++)
			classes[j] = Class.loadClass(config, jf, s);
		jf.classes = classes;
		jf.depends = depends;
		jf.nbPo = nbPo;
		jf.nbPoProved = nbPoProved;
		for (int j = 0; j < classes.length; j++)
			classes[j].setParent(jf);
		return jf;
	}

	/**
	 * The array of depends file.
	 **/
	private String[] depends;

	/**
	 * The array of classes
	 **/
	private Class[] classes;

	/**
	 * The currently displayed JML file
	 **/
	private File fileName;

	private File jpoFile;

	String[] langNames;
	
	boolean[] langGen;

	private int nbPo = -1;
	private int nbPoProved = -1;

	/*@
	  @ private invariant classes != null
	  @                && fileName != null;
	  @*/

	/**
	 * Constructs a jml file from loaded informations
	 * @param fileName The associated file
	 * @param classes The array of classes
	 **/
	/*@
	  @ requires fileName != null && classes != null;
	  @*/
	private JmlFile(String fileName, File jpoFile, String[] lang, boolean[] gen) {
		this.fileName = new File(fileName);
		this.jpoFile = jpoFile;
		langNames = lang;
		langGen = gen;
	}

	public void setChecked() {
		for (int i = 0; i < classes.length; i++)
			classes[i].setChecked();
	}

	public void setUnchecked() {
		for (int i = 0; i < classes.length; i++)
			classes[i].setUnchecked();
	}

	public int getNbPoProved(String prover) {
		int res = 0;
		for (int i = 0; i < classes.length; i++)
			res += classes[i].getNbPoProved(prover);
		return res;
	}

	public int getNbCheckedPo() {
		int res = 0;
		for (int i = 0; i < classes.length; i++)
			res += classes[i].getNbCheckedPo();
		return res;
	}

	public int getNbPo() {
		if (nbPo == -1) {
			int res = 0;
			for (int i = 0; i < classes.length; i++)
				res += classes[i].getNbPo();
			nbPo = res;
			return res;
		} else
			return nbPo;
	}

	public int getNbPoProved() {
		if (nbPoProved == -1) {
			int res = 0;
			for (int i = 0; i < classes.length; i++)
				res += classes[i].getNbPoProved();
			nbPoProved = res;
			return res;
		} else
			return nbPoProved;
	}

	public void updateStatus() {
		int res = 0;
		for (int i = 0; i < classes.length; i++)
			res += classes[i].getNbPo();
		nbPo = res;
		res = 0;
		for (int i = 0; i < classes.length; i++)
			res += classes[i].getNbPoProved();
		nbPoProved = res;
	}

	/**
	 * Saves the JML file into a
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The output stream representing the jpo file
	 * @throws IOException
	 **/
	public void save(IJml2bConfiguration config, JpoOutputStream s) throws IOException {
		s.writeInt(jml2b.structure.java.JmlFile.JPO_FILE_FORMAT_VERSION);
		s.writeUTF(fileName.getAbsolutePath());
		s.writeInt(getNbPo());
		s.writeInt(getNbPoProved());
		s.writeInt(langNames.length);
        for (int i=0; i < langNames.length; i++) {
			s.writeUTF(langNames[i]);
			s.writeBoolean(langGen[i]);
			if (Languages.getProverStatusClass(langNames[i]) == null)
				s.writeInt(0);
			else
				s.writeInt(getNbPoProved(langNames[i]));
			}
		s.writeInt(depends.length);
		for (int j = 0; j < depends.length; j++)
			s.writeUTF(depends[j]);

		s.writeInt(classes.length);
		for (int i = 0; i < classes.length; i++)
			classes[i].save(config, s, this);
	}

	/**
	 * Sets all the goals of this JML file to unprove.
	 **/
	public void unprove() {
		for (int i = 0; i < classes.length; i++)
			classes[i].unprove();
	}

//	/**
//	 * Returns the name of the B machine associated with this file
//	 * @return the name without extension
//	 **/
//	String getBMachineName() {
//		// get the name of the file part
//		String name = fileName.getName();
//		int ext_index = name.lastIndexOf('.');
//		if (ext_index > 0) {
//			name = name.substring(0, ext_index);
//		}
//		return name;
//	}

	/**
	 * @return the file name
	 **/
	public String getText(int type) {
		return fileName.getName();
	}

	/**
	  * Returns the currently displayed file
	  * @return <code>fileName</code>
	  **/
	public File getFileName() {
		return fileName;
	}

	/**
	 * Returns the array of classes.
	 * @return <code>classes</code>
	 **/
	public Class[] getClasses() {
		return classes;
	}

	/**
	 * @return
	 */
	public String[] getLangNames() {
		return langNames;
	}

	public void freeLemmas() {
		for (int i = 0; i < classes.length; i++)
			classes[i].freeLemmas();
	}

	/**
	 * @return
	 */
	public File getJpoFile() {
		return jpoFile;
	}

	/**
	 * @return
	 */
	public String[] getDepends() {
		return depends;
	}

	/**
	 * @param element
	 * @return
	 */
	public boolean dependsContains(String element) {
		for (int i = 0; i < depends.length; i++)
			if (depends[i].equals(element))
				return true;
		return false;
	}

	public List getGoals() {
		ArrayList al = new ArrayList();
		for (int i = 0; i < classes.length; i++)
			classes[i].addGoals(al);
		return al;
	}

	/**
	 * 
	 */
	public void finalizeLoad() {
		for (int i = 0; i < classes.length; i++)
			classes[i].finalizeLoad();
	}
	public void selectAll() {
		for (int i = 0; i < classes.length; i++)
			classes[i].selectAll();
	}
}
