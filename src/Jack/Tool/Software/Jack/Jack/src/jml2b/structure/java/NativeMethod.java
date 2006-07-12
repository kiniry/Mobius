/*
 * Created on Jan 25, 2006
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.structure.java;

import jml2b.pog.util.IdentifierResolver;


public class NativeMethod extends Method {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	Method m;
	
	public NativeMethod(Method m) {
		this.m = m;
	}

	public String getName() {
		return IdentifierResolver.getAbsoluteName(m.getDefiningClass()) + "_" + m.name;
	}

}
