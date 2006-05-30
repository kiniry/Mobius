package bytecode_wp.bytecode.conversioninstruction;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;

import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.BitExpression;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.LongNumberLiteral;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.vcg.VCGPath;

public class BCL2I extends BCConversionInstruction {
	/**
	 * @param _instruction
	 * 
	 * 
	 */
	public BCL2I(InstructionHandle _instruction) {
		super(_instruction);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return JavaType.JavaINT;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.BCTypedInstruction#setType(bcexpression.javatype.JavaType)
	 */
	public void setType(JavaType _type) {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bytecode.ByteCode#wp(formula.Formula,
	 *      specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config,
			Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		return null;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {

		BitExpression pMask = new BitExpression(new Stack(Expression.COUNTER),
				new LongNumberLiteral(0x00000000FFFFFFFF),
				ExpressionConstants.BITWISEAND);

		vcs.substitute(new Stack(Expression.COUNTER), pMask);

		return vcs;
	}
}
