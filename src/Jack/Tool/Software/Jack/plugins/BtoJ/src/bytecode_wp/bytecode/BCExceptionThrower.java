package bytecode_wp.bytecode;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcexpression.EXCEPTIONVariable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.bcexpression.ref.Reference;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.block.ControlFlowGraph;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate0Ar;
import bytecode_wp.utils.FreshIntGenerator;
import bytecode_wp.vcg.VCGPath;

/**
 * @author M. Pavlova
 * 
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates. To enable and disable the creation of type
 * comments go to Window>Preferences>Java>Code Generation.
 */
public abstract class BCExceptionThrower extends BCInstruction {
	private JavaObjectType[] exceptionsThrown;

	private ControlFlowGraph trace;

	/**
	 * @param _instruction
	 */
	public BCExceptionThrower(InstructionHandle _instruction) {
		super(_instruction);
	}

	/**
	 * initialises the exceptions for this instruction. Called in the
	 * constructor of instructions that are of type that extend this abstract
	 * class
	 * 
	 * @param _exceptionsThrown
	 */
	public void setExceptionsThrown(JavaObjectType[] _exceptionsThrown) {
		exceptionsThrown = _exceptionsThrown;
	}

	/**
	 * @return the array of exception types that this instruction may throw
	 */
	public JavaObjectType[] getExceptionsThrown() {
		return exceptionsThrown;
	}

	/***************************************************************************
	 * the method returns the postcondition that must be valid after this
	 * instruction throws an exception of type _exc_type
	 * 
	 * @see bytecode.ByteCode#wp(formula.Formula,
	 *      specification.ExceptionalPostcondition)
	 */
	public VCGPath getWpForException(IJml2bConfiguration config,
			JavaObjectType _exc_type) {
		//TODO Patch LB
		if (trace == null) {
			
			return VCGPath.initVCwithGoalFalse();
		}
		VCGPath _exc_termination = trace.getWpForExcThrownAt(config, _exc_type,
				getPosition());
		if (_exc_termination == null) {
			return VCGPath.initVCwithGoalFalse();
		}
		
		VCGPath _exc_termination_copy = (VCGPath) _exc_termination.copy();
		// set the stack top to
		_exc_termination_copy.substitute(
				new Stack(Expression.COUNTER), new Reference(FreshIntGenerator
						.getInt(), _exc_type));
		 _exc_termination_copy.substitute(
				new EXCEPTIONVariable(FreshIntGenerator.getInt(), _exc_type),
				new Reference(FreshIntGenerator.getInt(), _exc_type));
		return _exc_termination_copy;
	}

	public void setTrace(ControlFlowGraph _trace) {
		trace = _trace;
	}

	public ControlFlowGraph getTrace() {
		return trace;
	}
}
