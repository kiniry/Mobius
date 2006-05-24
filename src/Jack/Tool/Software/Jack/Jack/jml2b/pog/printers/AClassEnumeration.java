/*
 * Created on Apr 6, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.pog.printers;

import java.util.Enumeration;

import jml2b.structure.java.AClass;

/**
 *
 *  @author L. Burdy
 **/
public class AClassEnumeration {

	private Enumeration e;
	
	public AClassEnumeration(Enumeration e) {
		this.e = e;
	}
	
	public boolean hasMoreElements() {
		return e.hasMoreElements();
	}

	public AClass nextElement() {
		return (AClass) e.nextElement();
	}

}
