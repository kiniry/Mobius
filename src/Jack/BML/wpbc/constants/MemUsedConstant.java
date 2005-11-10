/*
 * Created on Mar 21, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package constants;

import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class MemUsedConstant extends BCConstantFieldRef {
	public static final MemUsedConstant MemUsedCONSTANT = new MemUsedConstant();

	private MemUsedConstant() {
	}
	
	public String toString() {
		return "_MEMUSED" ;
	}
	
	
	public boolean equals(Expression expr ) {
		if (expr == MemUsedCONSTANT ) {
			return true;
		}
		return false;
	}
	
	public BCConstantClass getConstantClass() {
		return null;
	}
}
