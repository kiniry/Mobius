/*
 * Created on Mar 30, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package constants;

import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ArrayLengthConstant  extends BCConstantFieldRef {

	
	public static final ArrayLengthConstant ARRAYLENGTHCONSTANT = new ArrayLengthConstant();
		
		
	private ArrayLengthConstant() {
	}
	
	public String toString() {
		return "_length" ;
	}
	
	
	public boolean equals(Expression expr ) {
		if (expr == ARRAYLENGTHCONSTANT) {
			return true;
		}
		return false;
	}
	
	public BCConstantClass getConstantClass() {
		return null;
	}

}
