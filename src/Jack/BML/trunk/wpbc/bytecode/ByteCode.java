/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import specification.ExceptionalPostcondition;
import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public interface ByteCode  {
	
	/**
	 * @return the wp for this bytecode
	 */
	public Formula wp(Formula _normal_Postcondition,   ExceptionalPostcondition _exc_Postcondition );
	
}
