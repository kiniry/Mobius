package bytecode_wp.bytecode.arithmetic;

import java.util.Vector;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;



import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.bytecode.BCTypedInstruction;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.vcg.Hypothesis;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 * 
 *	Operand Stack
 * ..., value1, value2 ==> ..., result
 * 
 * 
 * Description
 *
 *	Both value1 and value2 must be of type long. They are both popped from 
 *	the operand stack, and a signed integer comparison is performed. 
 * If value1 is greater than value2, the int value 1 is
 *	pushed onto the operand stack. If value1 is equal to value2, the int value 0 is pushed onto the operand stack. 
 * If value1 is less than value2, the int value -1 is pushed onto the operand stack.
 *
 *  
 */
public class BCLCMP extends BCInstruction implements BCTypedInstruction{
	//LCMP 

	/**
	 * @param _instruction
	 */
	public BCLCMP(InstructionHandle _instruction) {
		super(_instruction);

	}

	/* 
	 * returns the type  result of this instruction
	 * @see bytecode.BCTypedInstruction#getType()
	 */
	public JavaType getType() {
		return JavaType.JavaLONG;
	}

	/* (non-Javadoc)
	 * does nothing as the type of this instruction is by default long
	 * @see bytecode.BCTypedInstruction#setType(org.apache.bcel.generic.TypedInstruction, org.apache.bcel.generic.ConstantPoolGen)
	 */
	public void setType(JavaType _type) {
		
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		Vector wps = new Vector();
				
	
		
		// v1 == v2 => S(t)[t<--- t-1][S(t-1) <-- 0]
		Formula v1Equalsv2 = new Predicate2Ar(new Stack(Expression.COUNTER), new Stack(Expression.getCOUNTER_MINUS_1()), PredicateSymbol.EQ );
		Formula resultZero = (Formula)_normal_Postcondition.copy();
		resultZero.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		resultZero.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), new NumberLiteral(0));
		wps.add(Formula.getFormula(v1Equalsv2, resultZero, Connector.IMPLIES));
		
		 //	v1 >  v2 => S(t)[t<--- t-1][S(t-1) <-- 1]
		 Formula v1Grt2 = new Predicate2Ar( new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(Expression.COUNTER), PredicateSymbol.GRT);
		 Formula resultOne = (Formula)_normal_Postcondition.copy();
		 resultOne.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		 resultZero.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), new NumberLiteral(1));
		 wps.add( Formula.getFormula(v1Grt2 , resultOne, Connector.IMPLIES));
		 
		 
		//	v1 < v2 => S(t)[t<--- t-1][S(t-1) <-- 0]
		Formula v1Less2 = new Predicate2Ar( new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(Expression.COUNTER), PredicateSymbol.LESS);
		Formula resultMinusOne = (Formula)_normal_Postcondition.copy();
		resultOne.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		resultZero.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), new NumberLiteral(-1));
		wps.add( Formula.getFormula(v1Less2 , resultMinusOne, Connector.IMPLIES));
	 
	 	wp = Formula.getFormula(wps, Connector.AND);
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		
				
		//Stack topStack = new Stack(Expression.COUNTER);
//		Stack topStack_minus_1 = new Stack(Expression.COUNTER_MINUS_1);
		
		VCGPath vcEquiv1 = (VCGPath) vcs.copy();
		
		// v1 == v2 => S(t)[t<--- t-1][S(t-1) <-- 0]
		Formula v1Equalsv2 = new Predicate2Ar(new Stack(Expression.COUNTER), new Stack(Expression.getCOUNTER_MINUS_1()), PredicateSymbol.EQ );
		
		vcEquiv1.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		vcEquiv1.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), new NumberLiteral(0));
		// Hypothesis hyp1 = new Hypothesis(getPosition(), v1Equalsv2) ; 
		Integer key1 = vcEquiv1.addHyp(getPosition(), v1Equalsv2 );
		vcEquiv1.addHypsToVCs(key1);
		          
		VCGPath vcEquiv2 = (VCGPath) vcs.copy();
		 //	v1 >  v2 => S(t)[t<--- t-1][S(t-1) <-- 1]
		 Formula v1Grt2 = new Predicate2Ar( new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(Expression.COUNTER), PredicateSymbol.GRT);
		 v1Grt2.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		 v1Grt2.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), new NumberLiteral(1));
		 //Hypothesis hyp2 = new Hypothesis(getPosition(), v1Grt2);
		 
		 Integer key2 = vcEquiv2.addHyp(getPosition(), v1Grt2);
		 vcEquiv2.addHypsToVCs( key2);
		 //wps[1] = Formula.getFormula(v1Grt2 , resultOne, Connector.IMPLIES);
		 
		 
		//	v1 < v2 => S(t)[t<--- t-1][S(t-1) <-- 0]
		Formula v1Less2 = new Predicate2Ar( new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(Expression.COUNTER), PredicateSymbol.LESS);
		//Formula resultMinusOne = (Formula)_normal_Postcondition.copy();
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		vcs.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), new NumberLiteral(-1));
		
		/*Hypothesis hyp3 = new Hypothesis( getPosition(), v1Less2); 
		*/
		Integer key3 = vcs.addHyp(getPosition(), v1Less2);
		vcs.addHypsToVCs( key3);
	 
	 	vcs.merge(vcEquiv1);
	 	vcs.merge( vcEquiv2);
		return vcs;
	}

}


