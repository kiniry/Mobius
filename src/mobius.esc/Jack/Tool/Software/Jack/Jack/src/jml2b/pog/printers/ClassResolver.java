//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.pog.printers;

import java.util.Enumeration;
import java.util.HashSet;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.java.AClass;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.Package;
import jml2b.structure.statement.MyToken;
import jml2b.util.Profiler;

/**
 * @author L. Burdy
 **/
public class ClassResolver 
	extends Profiler
	implements MyToken, JmlDeclParserTokenTypes, IClassResolver {

//	/**
//	 * The print stream corresponding to the file
//	 **/
//	PrintStream stream;

	/**
	 * The set of interfaces currenlty accessible from root package 
	 **/
	HashSet interfaces;

	/**
	 * The set of classes currenlty accessible from root package 
	 **/
	HashSet classes;

	/*@
	  @ invariant interfaces != null
	  @        && classes != null;
	  @*/

	/**
	 * Constructs a file printer. Collects all accessible interfaces and classes.
	 **/
	public ClassResolver(JavaLoader p) {
		interfaces = new HashSet();
		classes = new HashSet();
		getClassesAndInterfaces(p.getRoot());
	}

	/**
	 * Collects all the accessible classes and interfaces from a package
	 * @param p The package
	 **/
	private void getClassesAndInterfaces(Package p) {
		Enumeration e = p.getSubPackages();
		// add classes and interfaces from subpackages
		while (e.hasMoreElements()) {
			Package tmp_pkg = (Package) e.nextElement();
			getClassesAndInterfaces(tmp_pkg);
		}

		// add classes from this package
		e = p.getClasses();
		while (e.hasMoreElements()) {
			AClass c = (AClass) e.nextElement();
			IdentifierResolver.addIdent(c);
			if (c.isInterface()) {
				interfaces.add(c);
			} else {
				classes.add(c);
			}
		}
	}

	public Vector getJmlFiles() {
		Vector res = new Vector();
		AClassEnumeration e = new ClassIterator(classes);
		while (e.hasMoreElements()) {
			AClass c = (AClass) e.nextElement();
			if (c.getJmlFile() != null) {
			String jf = c.getJmlFile().getFileName().getAbsolutePath();
			if (res.indexOf(jf) == -1)
				res.add(jf);
			}
		}
		e = new ClassIterator(interfaces);
		while (e.hasMoreElements()) {
			AClass c = (AClass) e.nextElement();
			if (c.getJmlFile() != null) {
			String jf = c.getJmlFile().getFileName().getAbsolutePath();
			if (res.indexOf(jf) == -1)
				res.add(jf);
			}
		}
		return res;
	}


	/**
	 * @return
	 */
	public AClassEnumeration getClasses() {
		return new ClassIterator(classes);
	}

	/**
	 * @return
	 */
	public AClassEnumeration getInterfaces() {
		return new ClassIterator(interfaces);
	}

}
