package bytecode;



import org.apache.bcel.generic.InstructionHandle;

import formula.Formula;
import formula.atomic.Predicate;
import formula.atomic.Predicate0Ar;

import utils.FreshIntGenerator;

import bcclass.attributes.ExsuresTable;
import bcexpression.EXCEPTIONVariable;
import bcexpression.Expression;
import bcexpression.ref.Reference;
import bcexpression.vm.Stack;

import bcexpression.javatype.JavaObjectType;
import bytecode.block.*;

/**
 * @author M. Pavlova
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public abstract class BCExceptionThrower extends BCInstruction {
	private JavaObjectType[] exceptionsThrown;
	
	private Trace trace;

	/**
	 * @param _instruction
	 */
	public BCExceptionThrower(InstructionHandle _instruction) {
		super(_instruction);
	}

	/**
	 * initialises  the exceptions for this instruction.
	 * Called in the constructor of instructions that are of  type that extend this abstract class 
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


	/* *
	 * the method returns the postcondition that must  be valid 
	 * after this instruction throws an exception of type _exc_type
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula getWpForException(
		JavaObjectType _exc_type) {
			Formula _exc_termination = trace.getWpForExcThrownAt(_exc_type, getPosition());
			if (_exc_termination == null) {
				return Predicate0Ar.FALSE;
			}
			if ((_exc_termination == Predicate0Ar.FALSE) || ( _exc_termination == Predicate0Ar.TRUE)) {
				return _exc_termination;
			}
			Formula _exc_termination_copy = (Formula)_exc_termination.copy();
			// set the stack top to 
			_exc_termination_copy =  (Formula)_exc_termination_copy.substitute(new Stack( Expression.COUNTER) , new Reference(FreshIntGenerator.getInt() , _exc_type));
			_exc_termination_copy = (Formula)_exc_termination_copy.substitute(
				new EXCEPTIONVariable(FreshIntGenerator.getInt(), _exc_type),
				new Reference(FreshIntGenerator.getInt(), _exc_type));
			return _exc_termination_copy;
	}	

	public void setTrace(Trace _trace) {
		trace = _trace;
	}
	
	public Trace  getTrace() {
		return trace;
	}
}
