/*
 * Created on Apr 20, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.stackinstruction;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;



import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.ArithmeticExpression;
import bytecode_wp.bcexpression.DummyVariable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 * 
 * NB: should take off the part for long / computational type 2
 * 
 * Operation : Duplicate the top operand stack value and insert two values down
 * 
 * Stack : ..., value2, value1 ==> ..., value1, value2, value1
 * 
 * Description: Duplicate the top value on the operand stack and insert the
 * duplicated value two values down in the operand stack.
 * 
 * psi^n = psi^n[t <-- t+1][S(t+1) <-- S(t)][S(t)<-- S(t-1)][S(t-1) <-- S(t )]
 */
public class BCDUP_X1 extends BCInstruction implements BCStackInstruction {

	/**
	 * @param _instruction
	 */
	public BCDUP_X1(InstructionHandle _instruction) {
		super(_instruction);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.ByteCode#wp(formula.Formula,
	 *      specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config,
			Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;

		wp = (Formula) _normal_Postcondition.substitute(Expression.COUNTER,
				Expression.getCOUNTER_PLUS_1());
		wp = (Formula) wp.substitute(new Stack(Expression.getCOUNTER_PLUS_1()),
				new Stack(Expression.COUNTER));
		wp = (Formula) wp.substitute(new Stack(Expression.COUNTER), new Stack(
				Expression.getCOUNTER_MINUS_1()));
		wp = (Formula) wp.substitute(
				new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(
						Expression.COUNTER));

		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		vcs.substitute(new Stack(Expression.getCOUNTER_MINUS_2()), new Stack(
				Expression.COUNTER));
/*		Expression v = new DummyVariable();
		vcs.substitute(new Stack(new ArithmeticExpression(Stack.COUNTER,
				new NumberLiteral(-1), ExpressionConstants.ADD)), v);

		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_1());
		vcs.substitute(new Stack(Expression.getCOUNTER_PLUS_1()), new Stack(
				Expression.COUNTER));
		vcs.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(
				Expression.COUNTER));
		vcs.substitute(v, new Stack(new ArithmeticExpression(Stack.COUNTER,
				new NumberLiteral(-1), ExpressionConstants.ADD)));*/
		return vcs;
	}
}
