package bytecode.loadstoreinstruction;

import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.InstructionHandle;


import formula.Formula;

import bcclass.attributes.ExsuresTable;
import bcexpression.ArithmeticExpression;
import bcexpression.BCLocalVariable;
import bcexpression.ExpressionConstants;
import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaType;


/**
 * @author mpavlova
 *
 * iinc 	index 	const
 * No changes on the stack are done.
 * 
 *  The index is an unsigned byte that must be an index into the local variable array of the current frame . 
 * The const is an immediate signed byte. The local variable at index must contain an int. 
 * The value const is first sign-extended to an int, and then the local variable at index is incremented by that amount.
 *  	
 */
public class BCIINC extends BCLocalVariableInstruction {

	/**
	 * the value by which the local variable will be incremented
	 */
	private NumberLiteral constant;
	
	public BCIINC(InstructionHandle _instruction, BCLocalVariable _lv) {
		super(_instruction, _lv);
		setType(JavaType.JavaINT);
		setConstant(((IINC) (_instruction.getInstruction())).getIncrement());
	}

	/**
	 * @see bytecode.BCLocalVariableInstruction#BCLocalVariableInstruction()
	 */
	public void BCLocalVariableInstruction() {
	}

	/**
	 * @param literal
	 */
	public void setConstant(int literal) {
		constant = new NumberLiteral(literal);
	}
	/**
	 * @param literal
	 */
	public NumberLiteral getConstant() {
		return constant;
	}

	/**
		 * @see bytecode.BCInstruction#wp(formula.Formula, specification.ExceptionalPostcondition)
		 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;
		ArithmeticExpression inc = (ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(constant, getLocalVariable(), ExpressionConstants.ADD ) ;
		wp = (Formula)_normal_Postcondition.substitute(getLocalVariable(), inc);
		return wp; 
	}

}
