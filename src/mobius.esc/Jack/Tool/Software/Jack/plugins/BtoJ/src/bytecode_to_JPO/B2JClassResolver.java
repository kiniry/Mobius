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

import java.util.Enumeration;
import java.util.HashSet;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.pog.printers.AClassEnumeration;
import jml2b.pog.printers.ClassIterator;
import jml2b.pog.printers.IClassResolver;
import bytecode_wp.bcclass.BCClass;

/**
 *
 *  @author L. Burdy
 **/
public class B2JClassResolver implements IClassResolver {

	HashSet classes;
	HashSet interfaces;
	
	public B2JClassResolver(IJml2bConfiguration config, B2JPackage ja, BCClass clazz) {
		classes = new HashSet();
		interfaces = new HashSet();
		Enumeration e = ja.getClasses().elements();
		while (e.hasMoreElements()) {
			BCClass element = (BCClass) e.nextElement();
			classes.add(((B2JPackage) config.getPackage()).addB2JClass(config, element, false));
			
		}
	}
	
	public AClassEnumeration getClasses() {
		return new ClassIterator(classes);
	}
	public AClassEnumeration getInterfaces() {
		return new ClassIterator(interfaces);
	}
	public Vector getJmlFiles() {
		return new Vector();
	}
}
