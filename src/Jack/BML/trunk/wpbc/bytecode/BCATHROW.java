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
public class BCATHROW extends BCExceptionThrower implements EndBlock {

	private JavaReferenceType exceptionThrown;

	/**
	 * @param _branchInstruction
	 */
	public BCATHROW(InstructionHandle _branchInstruction) {
		super(_branchInstruction);
		setInstructionCode(BCInstructionCodes.ATHROW);
		setExceptionThrown();
		//dump(_branchInstruction.toString() + " throws "  + getExceptions().length);	
	}

	/**
	 * sets the exception that this particular athrow instruction throws
	 */
	private void setExceptionThrown() {
		exceptionThrown = getExceptions()[0];
	}

	/**
	 * gets the exception that this particular athrow instruction throws
	 */
	private JavaReferenceType getExceptionThrown() {
		return exceptionThrown;
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
	public Formula wp(
		Formula _normal_Postcondition,
		ExceptionalPostcondition _exc_Postcondition) {
			
	    //wp for athrow by definition : 
	    //if there is a handle that can handle the exception thrown by this instruction then the 
	    //wp for the exception handle is returned, else 
	    // the exceptional postcondition specified in the specification for this exception is returned. 
	    // this is done by the method getWpForException in BCExceptionThrower
		Formula  wp = getWpForException(exceptionThrown, _exc_Postcondition);
		return wp;
	}

}
