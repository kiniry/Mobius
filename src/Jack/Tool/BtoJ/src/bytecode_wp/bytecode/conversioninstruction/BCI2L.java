package bytecode_wp.bytecode.conversioninstruction;

import org.apache.bcel.generic.InstructionHandle;

import jml2b.IJml2bConfiguration;
import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.BitExpression;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.LongNumberLiteral;
import bytecode_wp.bcexpression.javatype.JavaBasicType;
import bytecode_wp.bcexpression.javatype.JavaReferenceType;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 *
 * I2L
 * Convert int to long
 * 
 *  ..., value === >..., result
 * 
 * The value on the top of the operand stack must be of type int. 
 * It is popped from the operand stack, truncated to a byte, then sign-extended to an int result. 
 * That result is pushed onto the operand stack.
 * 
 * S(t) >= 0 => psi^n[S(t) <-- S(t) | 0x0000000000000000] 
 * &&
 * S(t) < 0 => psi^n[S(t) <-- S(t)  | 0x1111111100000000] 
 * 
 */
public class BCI2L extends BCConversionInstruction  {

	/**
	 * @param _instruction
	 */
	public BCI2L(InstructionHandle _instruction) {
		super(_instruction);
	}
	
	public JavaType getType() {
		// TODO Auto-generated method stub
		return JavaBasicType.JavaLONG;
	}

	public void setType(JavaType _type) {
		// TODO Auto-generated method stub
		
	}

	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		
		return null;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		Formula  positive = new Predicate2Ar(new Stack(Expression.COUNTER), new LongNumberLiteral(0), PredicateSymbol.GRTEQ);
		BitExpression posExtend = new BitExpression(new Stack(Expression.COUNTER), new LongNumberLiteral( 0x00000000FFFFFFFF) , ExpressionConstants.BITWISEOR);
		/*VCGPath  posCase = (VCGPath) vcs.copy();*/
		vcs.substitute(new Stack(Expression.COUNTER), posExtend);
		Integer hPos = vcs.addHyp(getPosition(), positive);
		vcs.addHypsToVCs( hPos);

		
/*		Formula  neg = new Predicate2Ar(new Stack(Expression.COUNTER), new LongNumberLiteral(0), PredicateSymbol.LESS);
		//BitExpression nMask = new BitExpression(new Stack(Expression.COUNTER), new NumberLiteral(0xFF), ExpressionConstants.BITWISEAND);
		BitExpression nExtend = new BitExpression(new Stack(Expression.COUNTER), new LongNumberLiteral( (long)( 0xFFFFFFFF << 32) & 0x00000000FFFFFFFF) , ExpressionConstants.BITWISEOR);
		
		Formula nCopy = (Formula)_normal_Postcondition.copy();
		vcs.substitute(new Stack(Expression.COUNTER), nExtend);
		Integer hNeg = vcs.addHyp( getPosition(), neg);
		vcs.addHypsToVCs( hNeg);
		vcs.merge( posCase);*/
		
		
		return vcs;
	}
	
	

}
