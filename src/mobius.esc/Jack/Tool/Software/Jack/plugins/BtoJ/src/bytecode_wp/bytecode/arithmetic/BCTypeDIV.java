/*
 * Created on Apr 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.arithmetic;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.IDIV;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LDIV;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.ArithmeticExpression;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCConstants;
import bytecode_wp.bytecode.BCInstructionCodes;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.vcg.Hypothesis;
import bytecode_wp.vcg.VC;
import bytecode_wp.vcg.VCGPath;
import bytecode_wp.vcg.VcType;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCTypeDIV extends BCArithmeticInstructionWithException {

	
	/**
	 * @param _instruction
	 * @param _type
	 */
	public BCTypeDIV(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		if (_instruction.getInstruction() instanceof IDIV) {
			setArithmeticOperation(BCConstants.DIV_INT);
			setInstructionCode(BCInstructionCodes.IDIV);
		} else if (_instruction.getInstruction() instanceof LDIV) {
			setArithmeticOperation(BCConstants.DIV_LONG);
			setInstructionCode(BCInstructionCodes.LDIV);
		}

	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		IJml2bConfiguration config,
		Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {


		return null;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		
		Formula divisorNonZero =
			Formula.getFormula(new Predicate2Ar(
				new Stack(Expression.COUNTER),
				new NumberLiteral(0),
				PredicateSymbol.EQ) , Connector.NOT );
		ArithmeticExpression divResult =
			(ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(
				new Stack(Expression.getCOUNTER_MINUS_1()),
				new Stack(Expression.COUNTER),
				ExpressionConstants.DIV);
		vcs.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_1());
		vcs.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), divResult);
		//Hypothesis hypDivNon0  =new Hypothesis(getPosition(),divisorNonZero);
		Integer key1 = vcs.addHyp( getPosition(),divisorNonZero);
		vcs.addHypsToVCs( key1);
		
		/*Formula wpNormalExecution =
		Formula.getFormula(
				divisorNonZero,
				_normal_Postcondition,
				Connector.IMPLIES);*/
		//stack(top ) == null 
		Formula divisorIsZero =
			new Predicate2Ar(
				new Stack(Expression.COUNTER),
				new NumberLiteral(0),
				PredicateSymbol.EQ);

		//_excPost = if exists exceptionHandler for NullPointerException then  wp(exceptionHandler,  normalPost) else 
		//                  else ExcPostcondition 
		VCGPath _excPost =
			getWpForException(config, 
				(JavaObjectType) JavaType.getJavaRefType(
					"Ljava/lang/ArithmeticException;"));
		Integer key2  = _excPost.addHyp(getPosition(),divisorIsZero);
		_excPost.addHypsToVCs( key2);
		vcs.merge( _excPost);
		return vcs;
		
		
		
		// stack(top)  != null ==>�_normal_Postcondition[t <-- t-1][S(t-1) <-- S(t-1) / S(t)] 
		// &&
		// stack(top)  == null ==> excPost
		
		
	}


}
