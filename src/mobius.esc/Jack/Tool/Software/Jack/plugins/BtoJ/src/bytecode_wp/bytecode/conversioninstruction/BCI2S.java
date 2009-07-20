/*
 * Created on Apr 16, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.conversioninstruction;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.BitExpression;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.vcg.Hypothesis;
import bytecode_wp.vcg.VCGPath;
/**
 * @author mpavlova
 *I2S
 *Convert int to short
 * 
 *  ..., value === >..., result
 * 
 * The value on the top of the operand stack must be of type int. 
 * It is popped from the operand stack, truncated to a byte, 
 * then sign-extended to an int result. 
 * That result is pushed onto the operand stack.
 * 
 * S(t) >= 0 => psi^n[S(t) <-- (S(t) &0xFF)] 
 * &&
 * S(t) < 0 => psi^n[S(t) <-- (S(t) &0xFF) | 0x11110000] 
 */
public class BCI2S extends BCConversionInstruction  {

	/**
	 * @param _instruction
	 * 
	 * 
	 */
	public BCI2S(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return JavaType.JavaBYTE;
	}

	/* (non-Javadoc)
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
//		Stack stackTop = new Stack(Expression.COUNTER);
		
		Formula  positive = new Predicate2Ar(new Stack(Expression.COUNTER), new NumberLiteral(0), PredicateSymbol.GRTEQ);
		BitExpression pMask = new BitExpression(new Stack(Expression.COUNTER), new NumberLiteral(0xFFFF), ExpressionConstants.BITWISEAND);
		Formula pCopy = (Formula)_normal_Postcondition.copy();
		pCopy.substitute(new Stack(Expression.COUNTER), pMask);
		Formula wpPositive = Formula.getFormula(positive, pCopy, Connector.IMPLIES);
		
		Formula  neg = new Predicate2Ar(new Stack(Expression.COUNTER), new NumberLiteral(0), PredicateSymbol.LESS);
		BitExpression nMask = new BitExpression(new Stack(Expression.COUNTER), new NumberLiteral(0xFFFF), ExpressionConstants.BITWISEAND);
		BitExpression nExtend = new BitExpression(nMask, new NumberLiteral(0xFFFF0000), ExpressionConstants.BITWISEOR);
		Formula nCopy = (Formula)_normal_Postcondition.copy();
		pCopy.substitute(new Stack(Expression.COUNTER), nExtend);
		Formula wpNeg = Formula.getFormula(positive, pCopy, Connector.IMPLIES);
		
		wp = Formula.getFormula(wpPositive, wpNeg, Connector.AND);
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		Formula  positive = new Predicate2Ar(new Stack(Expression.COUNTER), new NumberLiteral(0), PredicateSymbol.GRTEQ);
		BitExpression pMask = new BitExpression(new Stack(Expression.COUNTER), new NumberLiteral(0xFFFF), ExpressionConstants.BITWISEAND);
		vcs.substitute(new Stack(Expression.COUNTER), pMask);
		Integer hPos = vcs.addHyp( getPosition(), positive);
		//add the hypothesis for all goals
		vcs.addHypsToVCs( hPos);
		return vcs;
	}

}
