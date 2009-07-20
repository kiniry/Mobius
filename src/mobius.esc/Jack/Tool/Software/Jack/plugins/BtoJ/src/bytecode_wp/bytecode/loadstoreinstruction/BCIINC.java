package bytecode_wp.bytecode.loadstoreinstruction;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.InstructionHandle;

import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.ArithmeticExpression;
import bytecode_wp.bcexpression.BCLocalVariable;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 * 
 * iinc index const No changes on the stack are done.
 * 
 * The index is an unsigned byte that must be an index into the local variable
 * array of the current frame . The const is an immediate signed byte. The local
 * variable at index must contain an int. The value const is first sign-extended
 * to an int, and then the local variable at index is incremented by that
 * amount.
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

	public Formula wp(IJml2bConfiguration config,
			Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		ArithmeticExpression inc = (ArithmeticExpression) ArithmeticExpression
				.getArithmeticExpression(constant, getLocalVariable(),
						ExpressionConstants.ADD);
		wp = (Formula) _normal_Postcondition
				.substitute(getLocalVariable(), inc);
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		ArithmeticExpression inc = (ArithmeticExpression) ArithmeticExpression
				.getArithmeticExpression(getLocalVariable(), constant,
						ExpressionConstants.ADD);
		vcs.substitute(getLocalVariable(), inc);
		return vcs;
	}

}
