/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;


import java.util.Vector;

import org.apache.bcel.generic.ConstantPoolGen;

import vm.Stack;

import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public interface ByteCode  {
	
	/**
	 * 
	 * @return a vector of formulas that should be valid before execution of the bytecode
	 */
	public Formula wp(Formula _normal_Postcondition,Formula  _exc_Postcondition, Stack stack, ConstantPoolGen _cp);

}
