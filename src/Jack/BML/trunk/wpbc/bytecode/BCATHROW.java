/*
 * Created on Mar 1, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.InstructionHandle;

import utils.Util;

import formula.Formula;
import formula.atomic.Predicate0Ar;

import bcclass.attributes.ExceptionHandler;
import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;
import bcexpression.jml.TYPEOF;
import bcexpression.overload.FormulaOverload;
import bcexpression.vm.Stack;

//import bytecode.block.*;

/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCATHROW extends BCExceptionThrower {

	//	private Block blockEndingWithThis;
	/**
	 * @param _branchInstruction
	 */
	public BCATHROW(InstructionHandle _throwInstruction) {
		super(_throwInstruction);
		setInstructionCode(BCInstructionCodes.ATHROW);
		setExceptionThrown(_throwInstruction);
		//dump(_branchInstruction.toString() + " throws " +
		// getExceptions().length);
	}

	/**
	 * sets the exception that this particular athrow instruction throws
	 */
	private void setExceptionThrown(InstructionHandle _throwInstruction) {
		Class excThrownClass = ((ATHROW) _throwInstruction.getInstruction())
				.getExceptions()[0];

		JavaObjectType excThrown = (JavaObjectType) JavaType
				.getJavaRefType(excThrownClass.getName());
		super.setExceptionsThrown(new JavaObjectType[] { excThrown });
	}

	/**
	 * gets the exception that this particular athrow instruction throws
	 */
	public JavaObjectType getExceptionThrown() {
		return getExceptionsThrown()[0];
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.ByteCode#wp(formula.Formula,
	 *      specification.ExceptionalPostcondition)
	 */
	public Formula wp(Formula _normal_Postcondition,
			ExsuresTable _exc_Postcondition) {
		Stack topStack = new Stack(Expression.COUNTER);
		Expression typeOfTopStack = new TYPEOF(topStack);

		// check if there is any information about the checked or thrown
		// exception as well if there
		// are exsures clause
		JavaObjectType[] exceptionsThrown = getTrace().getMethod()
				.getExceptionsThrown();
		ExceptionHandler[] excHandlers = getTrace().getMethod()
				.getExceptionHandlers();

		// in case there is no any specified exception then any thrown exception
		// implies false
		// in the post state
		if ((exceptionsThrown == null || exceptionsThrown.length == 0)
				&& (excHandlers == null || excHandlers.length == 0)
				&& (_exc_Postcondition == null
						|| _exc_Postcondition.getExsures() == null || _exc_Postcondition
						.getExsures().length == 0)) {
			return Predicate0Ar.FALSE;
		}
		FormulaOverload wp = new FormulaOverload(getTrace(), typeOfTopStack,
				this);
		return wp;
	}

}