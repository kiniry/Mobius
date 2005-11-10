/*
 * Created on Apr 20, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.stackinstruction;

import org.apache.bcel.generic.InstructionHandle;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;
import bcclass.attributes.ExsuresTable;
import bcexpression.Expression;

import bcexpression.javatype.JavaType;
import bcexpression.vm.Stack;
import bytecode.BCInstruction;

/**
 * @author mpavlova
 *
 *  NB: should take off the part for long / computational type 2
 * 
 * Operation:  Duplicate the top operand stack value and insert two or three values down
 * 
 * Format : dup_x2
 * 
 * Operand Stack
 *
 *  Form 1:
 *
 *   ..., value3, value2, value1 ==>..., value1, value3, value2, value1
 *
 *  where value1, value2, and value3 are all values of a category 1 computational type 
 *
 *   Form 2:
 *
 *   ..., value2, value1 ==> ..., value1, value2, value1
 *
 *   where value1 is a value of a category 1 computational type and value2 is a value of a category 2 computational type 
 * 
 * wp = (S(t-2), S(t - 1), S(t) instanceof  CompType1)  == > psi^n[t <-- t+1][S(t+1) <-- S(t)][S(t)<-- S(t-1)][S(t-1) <-- S(t -2 )][S(t-2) <-- S(t )]
 * 		&&
 * 		(S(t) instanceof  CompType1 and S(t - 1) instanceof  CompType2)  == > psi^n[t <-- t+1][S(t+1) <-- S(t)][S(t)<-- S(t -1)][S(t - 1)<-- S(t )]
 * 
 */
public class BCDUP_X2 extends BCInstruction implements BCStackInstruction {

	/**
	 * @param _instruction
	 */
	public BCDUP_X2(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		Formula _normal_Postcondition,
		ExsuresTable _exc_Postcondition) {
		Formula wp;

//		Stack stackTop_plus_1 = new Stack(Expression.COUNTER_PLUS_1);
//		Stack stackTop = new Stack(Expression.COUNTER);
//		Stack stackTop_minus_1 = new Stack(Expression.COUNTER_MINUS_1);
		Stack stackTop_minus_2 = new Stack(Expression.getCOUNTER_MINUS_2());
		///////////////////////////////////////////
		//////////////////first version of instruction execution
		///////////////////////////////////////////////////
		Formula[] three_on_stack_top_of_comp_type_1 = new Formula[3];
		// s (t-1) of comp type 1
		three_on_stack_top_of_comp_type_1[0] =
			new Predicate2Ar(
				((JavaType) new Stack(Expression.COUNTER).getType()).getComputationalType(),
				JavaType.COMPUTATIONAL_TYPE_1,
				PredicateSymbol.EQ);
		// s (t-1) of_comp_type_1
		three_on_stack_top_of_comp_type_1[1] =
			new Predicate2Ar(
				((JavaType) new Stack(Expression.getCOUNTER_MINUS_1()).getType()).getComputationalType(),
				JavaType.COMPUTATIONAL_TYPE_1,
				PredicateSymbol.EQ);
		//			s (t-2) of_comp_type_1
		three_on_stack_top_of_comp_type_1[1] =
			new Predicate2Ar(
				((JavaType) stackTop_minus_2.getType()).getComputationalType(),
				JavaType.COMPUTATIONAL_TYPE_1,
				PredicateSymbol.EQ);

		Formula condition_comp_type1 =
			Formula.getFormula(three_on_stack_top_of_comp_type_1, Connector.AND);

		// psi^n[t <-- t+1][S(t+1) <-- S(t)][S(t)<-- S(t-1)][S(t-1) <-- S(t -2 )][S(t-2) <-- S(t )]
		Formula f1 = (Formula)_normal_Postcondition.copy();
		f1 =
		(Formula)f1.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_PLUS_1());
		f1 = (Formula)f1.substitute(new Stack(Expression.getCOUNTER_PLUS_1()), new Stack(Expression.COUNTER));
		f1 = (Formula)f1.substitute(new Stack(Expression.COUNTER), new Stack(Expression.getCOUNTER_MINUS_1()));
		f1 = (Formula)f1.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), stackTop_minus_2);
		f1 = (Formula)f1.substitute(stackTop_minus_2, new Stack(Expression.COUNTER));

		//		 (S(t-2), S(t - 1), S(t) instanceof  CompType1)  == > psi^n[t <-- t+1][S(t+1) <-- S(t)][S(t)<-- S(t-1)][S(t-1) <-- S(t -2 )][S(t-2) <-- S(t )]
		Formula branch1 =
		Formula.getFormula(condition_comp_type1, f1, Connector.IMPLIES);

		//			/////////////////////////////////////////
		//			////////////////second version of instruction execution - dealing with long values
		//			/////////////////////////////////////////////////
		//S(t) instanceof Comp_type1
		Formula stackTop_ofComp_type1 =
			new Predicate2Ar(
				((JavaType) new Stack(Expression.COUNTER).getType()).getComputationalType(),
				JavaType.COMPUTATIONAL_TYPE_1,
				PredicateSymbol.EQ);
		//			S(t - 1) instanceof Comp_type2
		Formula stackTop_minus1_ofComp_type2 =
			new Predicate2Ar(
				((JavaType) new Stack(Expression.getCOUNTER_MINUS_1()).getType()).getComputationalType(),
				JavaType.COMPUTATIONAL_TYPE_2,
				PredicateSymbol.EQ);
		Formula condition =
		Formula.getFormula(
				stackTop_ofComp_type1,
				stackTop_minus1_ofComp_type2,
				Connector.AND);

		Formula f2 = (Formula)_normal_Postcondition.copy();
		f2 =
		(Formula)f2.substitute(
				Expression.COUNTER,
				Expression.getCOUNTER_PLUS_1());
		f2 = (Formula)f2.substitute(new Stack(Expression.getCOUNTER_PLUS_1()), new Stack(Expression.COUNTER));
		f2 = (Formula)f2.substitute(new Stack(Expression.COUNTER), new Stack(Expression.getCOUNTER_MINUS_1()));
		f2 = (Formula)f2.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(Expression.COUNTER));

		Formula branch2 = Formula.getFormula(condition, f2, Connector.IMPLIES);
		wp = Formula.getFormula(branch1, branch2, Connector.AND);
		return wp;
	}

}
