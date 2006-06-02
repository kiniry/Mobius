//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: 
 /*
 /* Created on Sep 29, 2004
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/
package bytecode_to_JPO;

import java.io.File;
import java.util.Enumeration;
import java.util.Vector;

import jml2b.structure.IPackage;

/**
 *
 *  @author L. Burdy
 **/
public class BCJmlFile extends jml2b.structure.java.JmlFile {

	/** */
	private static final long serialVersionUID = 1L;

	public int getNbPo() {
		return classzz.getNbPo();
	}
	public int getNbPoProved() {
		return classzz.getNbPoProved();
	}
	B2JClass classzz;
	String name;
	File ip;
	
	BCJmlFile(B2JClass classzz, String name, File ip) {
		this.classzz = classzz;
		this.name = name;
		this.ip = ip;
	}
	
	public String getFlatName() {
		return name;
	}

	/**
	 * Returns the "flat name" for this <code>JmlFile</code>.
	 * <p>
	 * The flat name is a name that can be used as a B machine name,
	 * and reduce the probability of name conflicts between different classes 
	 * (such as classes with the same name in different packages).
	 * <p>
	 * It is currently equal to the name of the package this file belongs to,
	 * with dots replaced by underscores, and the name of the file without 
	 * its extension.
	 * 
	 * In case where the file belongs to the default package, the flat name
	 * correspond to the name of the file, without its extension.
	 */
	public String getFlatName(IPackage p) {
		return getFlatName();
//		// get the name of the file part
//		String file_part = getFileName().getName();
//		int ext_index = file_part.lastIndexOf('.');
//		if (ext_index > 0) {
//			file_part = file_part.substring(0, ext_index);
//		}
//
//		if (filePackage == null/* || filePackage == p.getRoot()*/) {
//			// if the file belongs to the default package
//			return file_part;
//		} else {
//			return filePackage.getFullyQualifiedName(config).replace('.', '_')
//				+ "_"
//				+ file_part;
//		}
	}

	public Vector getDepends() {
		return new Vector();
	}

	public void mergeWith(jpov.structure.JmlFile jf) {
	}

	public void purgeObvious() {
	}

	public String getFileNameAbsolutePath() {
		return new File(ip.toString(), name + ".cod").toString();
		
	}
	public int getNbPoProved(String prover) {
		return getNbPoProved();
	}
	
	public Enumeration getClasses() {
		Vector res = new Vector();
		res.add(classzz);
		return res.elements();
	}


	
}
