//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.source;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;

/**
 * Content provider for the method list page.
 * 
 * @author L. Burdy
 **/
public class MethodListContentProvider implements IStructuredContentProvider {

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IStructuredContentProvider#getElements(java.lang.Object)
	 */
	public Object[] getElements(Object inputElement) {
		JmlFile jf = (JmlFile) inputElement;
		Vector methods = new Vector();
		Enumeration e = jf.getClasses();
		while (e.hasMoreElements()) {
			Class c = (Class) e.nextElement();
			methods.addAll(c.constructors);
			methods.addAll(c.methods);
		}
		return methods.toArray();
	}

	public void dispose() {
	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
	}

}
