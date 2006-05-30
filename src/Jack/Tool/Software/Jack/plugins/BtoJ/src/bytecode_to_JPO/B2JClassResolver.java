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
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.pog.printers.AClassEnumeration;
import jml2b.pog.printers.IClassResolver;
import bytecode_wp.bcclass.BCClass;

/**
 *
 *  @author L. Burdy
 **/
public class B2JClassResolver implements IClassResolver {

	Vector classes;
	Vector interfaces;
	
	public B2JClassResolver(IJml2bConfiguration config, B2JPackage ja, BCClass clazz) {
		classes = new Vector();
		interfaces = new Vector();
		Enumeration e = ja.getClasses().elements();
		while (e.hasMoreElements()) {
			BCClass element = (BCClass) e.nextElement();
			classes.add(((B2JPackage) config.getPackage()).addB2JClass(config, element, false));
			
		}
	}
	
	public AClassEnumeration getClasses() {
		return new AClassEnumeration(classes.elements());
	}
	public AClassEnumeration getInterfaces() {
		return new AClassEnumeration(interfaces.elements());
	}
	public Vector getJmlFiles() {
		return new Vector();
	}
}
