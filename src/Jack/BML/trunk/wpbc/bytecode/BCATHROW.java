/*
 * Created on Mar 1, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.InstructionHandle;

import formula.Formula;

import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;
import bcexpression.jml.TYPEOF;
import bcexpression.substitution.FormulaWITH;
import bcexpression.vm.Stack;
//import bytecode.block.*;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCATHROW
	extends BCExceptionThrower
 {

//	private Block blockEndingWithThis;
	/**
	 * @param _branchInstruction
	 */
	public BCATHROW(InstructionHandle _throwInstruction) {
		super(_throwInstruction);
		setInstructionCode(BCInstructionCodes.ATHROW);
		setExceptionThrown(_throwInstruction);
		//dump(_branchInstruction.toString() + " throws "  + getExceptions().length);	
	}

//	/* (non-Javadoc)
//		 * @see bytecode.EndBlockInstruction#setBlock(bytecode.block.Block)
//		 */
//	public void setBlock(Block block) {
//		blockEndingWithThis = block;
//	}

	/**
	 * sets the exception that this particular athrow instruction throws
	 */
	private void setExceptionThrown(InstructionHandle _throwInstruction) {
		Class excThrownClass =
			((ATHROW) _throwInstruction.getInstruction()).getExceptions()[0];

		JavaObjectType excThrown =
			(JavaObjectType) JavaType.getJavaRefType(excThrownClass.getName());
		super.setExceptionsThrown(new JavaObjectType[] { excThrown });
	}

	

	/**
	 * gets the exception that this particular athrow instruction throws
	 */
	public JavaObjectType getExceptionThrown() {
		return getExceptionsThrown()[0];
	}



	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {

	
		Stack topStack = new Stack(Expression.COUNTER);
		Expression typeOfTopStack = new TYPEOF(topStack); 
		FormulaWITH wp = new FormulaWITH( getTrace(), typeOfTopStack, this);
//		JavaObjectType excThrown = getExceptionThrown();
//		Formula wp =
//			getWpForException(excThrown, _exc_Postcondition);
		return wp;
	}

//	/* (non-Javadoc)
//	 * @see bytecode.EndBlockInstruction#calculateRecursively(formula.Formula, bcclass.attributes.ExsuresTable)
//	 */
//	public Formula calculateRecursively(
//		Formula _normal_postcondition,
//		ExsuresTable _exs_postcondition) {
//		Formula  wp = blockEndingWithThis.calculateRecursively(_normal_postcondition, _exs_postcondition);
//		return wp;
//	}

}
