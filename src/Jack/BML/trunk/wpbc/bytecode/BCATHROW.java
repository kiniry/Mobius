/*
 * Created on Mar 1, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import org.apache.bcel.generic.InstructionHandle;

import specification.ExceptionalPostcondition;
import formula.Formula;

import bcexpression.javatype.JavaReferenceType;


/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCATHROW extends BCExceptionThrower implements EndBlock{
	
	private JavaReferenceType exceptionThrown;

	/**
	 * @param _branchInstruction
	 */
	public BCATHROW(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
		//dump(_branchInstruction.toString() + " throws "  + getExceptions().length);	
	}
	
	/**
	 * @return the block that  handles
	 * that handles this exception; returns null if there is not any
	 */
	public Block getHandler() {
		return getExceptionHandleBlockForException(exceptionThrown);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition, ExceptionalPostcondition _exc_Postcondition)  {
		return _normal_Postcondition;
	}
	
	
}
