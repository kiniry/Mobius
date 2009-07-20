package bytecode_wp.bytecode.arithmetic;

import java.util.Hashtable;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.IREM;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LREM;


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
 * @author Mariela
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class BCTypeREM extends BCArithmeticInstructionWithException {
	
	
	private JavaObjectType[] exceptionsThrown ;
	private Hashtable excHandleBlocks;
	
	
	/**
	 * @param _instruction
	 */
	public BCTypeREM(InstructionHandle _instruction, JavaType _type) {
		super(_instruction, _type);
		if (_instruction.getInstruction() instanceof IREM) {
			setArithmeticOperation(BCConstants.REM_INT);
			setInstructionCode(BCInstructionCodes.IREM);
		} else if (_instruction.getInstruction() instanceof LREM) {
			setArithmeticOperation(BCConstants.REM_LONG);
			setInstructionCode(BCInstructionCodes.LREM);
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
			Formula.getFormula( new Predicate2Ar(
				new Stack(Expression.COUNTER),
				new NumberLiteral(0),
				PredicateSymbol.EQ) , Connector.NOT) ;
		ArithmeticExpression remResult =
			(ArithmeticExpression)ArithmeticExpression.getArithmeticExpression(
				new Stack(Expression.COUNTER),
				new Stack(Expression.getCOUNTER_MINUS_1()),
				ExpressionConstants.REM);
		vcs.substitute(
			Expression.COUNTER,
			Expression.getCOUNTER_MINUS_1());
		vcs.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), remResult);


		Integer key1 = vcs.addHyp( getPosition(), divisorNonZero);
		vcs.addHypsToVCs(key1);
		
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
		
		Integer key2= _excPost.addHyp(getPosition(), divisorIsZero);
		_excPost.addHypsToVCs(key2);
		
		vcs.merge(_excPost );
		return vcs; 
		
		// stack(top)  != null ==>_normal_Postcondition[t <-- t-1][S(t-1) <-- S(t-1) rem S(t)] 
		// &&
		// stack(top)  == null ==> excPost

	}

}
