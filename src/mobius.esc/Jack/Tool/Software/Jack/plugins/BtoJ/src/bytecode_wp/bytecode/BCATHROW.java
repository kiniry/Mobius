/*
 * Created on Mar 1, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExceptionHandler;
import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.jml.TYPEOF;
import bytecode_wp.bcexpression.overload.FormulaOverride;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate0Ar;
import bytecode_wp.vcg.VCGPath;
import bytecode_wp.vcg.VcType;

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
	public Formula wp(IJml2bConfiguration config,
			Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
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
		FormulaOverride wp = new FormulaOverride(config, getTrace(), typeOfTopStack,
				this);
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc_Postcondition) {
		Stack topStack = new Stack(Expression.COUNTER);
		Expression typeOfTopStack = new TYPEOF(topStack);

		// check if there is any information about the checked or thrown
		// exception as well if there
		// are exsures clause
		JavaObjectType[] exceptionsThrown = getTrace().getMethod()
				.getExceptionsThrown();
		ExceptionHandler[] excHandlers = getTrace().getMethod()
				.getExceptionHandlers();

		// in case there is no specified exception then any thrown exception
		// implies false
		// in the post state
		if ((exceptionsThrown == null || exceptionsThrown.length == 0)
				&& (excHandlers == null || excHandlers.length == 0)
				&& (_exc_Postcondition == null
						|| _exc_Postcondition.getExsures() == null || _exc_Postcondition
						.getExsures().length == 0)) {
			return VCGPath.initVCwithGoalFalse();
		}
		FormulaOverride wp = new FormulaOverride(config, getTrace(), typeOfTopStack,
				this);
		//VCGPath _vcs = new VCGPath();
		vcs.addGoal( VcType.INSTR_THROW_EXC , wp, getPosition());
		return vcs;
	}

}