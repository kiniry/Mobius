/*
 * Created on Apr 20, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.stackinstruction;

import java.util.Vector;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;

import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 * 
 * NB: should take off the part for long / computational type 2
 * 
 * Operation: Duplicate the top operand stack value and insert two or three
 * values down
 * 
 * Format : dup_x2
 * 
 * Operand Stack
 * 
 * Form 1:
 * 
 * ..., value3, value2, value1 ==>..., value1, value3, value2, value1
 * 
 * where value1, value2, and value3 are all values of a category 1 computational
 * type
 * 
 * Form 2:
 * 
 * ..., value2, value1 ==> ..., value1, value2, value1
 * 
 * where value1 is a value of a category 1 computational type and value2 is a
 * value of a category 2 computational type
 * 
 * wp = (S(t-2), S(t - 1), S(t) instanceof CompType1) == > psi^n[t <--
 * t+1][S(t+1) <-- S(t)][S(t)<-- S(t-1)][S(t-1) <-- S(t -2 )][S(t-2) <-- S(t )] &&
 * (S(t) instanceof CompType1 and S(t - 1) instanceof CompType2) == > psi^n[t
 * <-- t+1][S(t+1) <-- S(t)][S(t)<-- S(t -1)][S(t - 1)<-- S(t )]
 * 
 */
public class BCDUP_X2 extends BCInstruction implements BCStackInstruction {

	/**
	 * @param _instruction
	 */
	public BCDUP_X2(InstructionHandle _instruction) {
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

		Stack stackTop_minus_2 = new Stack(Expression.getCOUNTER_MINUS_2());
		// /////////////////////////////////////////
		// ////////////////first version of instruction execution
		// /////////////////////////////////////////////////
		Vector three_on_stack_top_of_comp_type_1 = new Vector();
		// s (t-1) of comp type 1
		three_on_stack_top_of_comp_type_1.add(new Predicate2Ar(
				((JavaType) new Stack(Expression.COUNTER).getType())
						.getComputationalType(), JavaType.COMPUTATIONAL_TYPE_1,
				PredicateSymbol.EQ));
		// s (t-1) of_comp_type_1
		three_on_stack_top_of_comp_type_1.add(new Predicate2Ar(
				((JavaType) new Stack(Expression.getCOUNTER_MINUS_1())
						.getType()).getComputationalType(),
				JavaType.COMPUTATIONAL_TYPE_1, PredicateSymbol.EQ));
		// s (t-2) of_comp_type_1
		three_on_stack_top_of_comp_type_1.add(new Predicate2Ar(
				((JavaType) stackTop_minus_2.getType()).getComputationalType(),
				JavaType.COMPUTATIONAL_TYPE_1, PredicateSymbol.EQ));

		Formula condition_comp_type1 = Formula.getFormula(
				three_on_stack_top_of_comp_type_1, Connector.AND);

		// psi^n[t <-- t+1][S(t+1) <-- S(t)][S(t)<-- S(t-1)][S(t-1) <-- S(t -2
		// )][S(t-2) <-- S(t )]
		Formula f1 = (Formula) _normal_Postcondition.copy();
		f1 = (Formula) f1.substitute(Expression.COUNTER, Expression
				.getCOUNTER_PLUS_1());
		f1 = (Formula) f1.substitute(new Stack(Expression.getCOUNTER_PLUS_1()),
				new Stack(Expression.COUNTER));
		f1 = (Formula) f1.substitute(new Stack(Expression.COUNTER), new Stack(
				Expression.getCOUNTER_MINUS_1()));
		f1 = (Formula) f1.substitute(
				new Stack(Expression.getCOUNTER_MINUS_1()), stackTop_minus_2);
		f1 = (Formula) f1.substitute(stackTop_minus_2, new Stack(
				Expression.COUNTER));

		// (S(t-2), S(t - 1), S(t) instanceof CompType1) == > psi^n[t <--
		// t+1][S(t+1) <-- S(t)][S(t)<-- S(t-1)][S(t-1) <-- S(t -2 )][S(t-2) <--
		// S(t )]

		Formula branch1 = Formula.getFormula(condition_comp_type1, f1,
				Connector.IMPLIES);

		// /////////////////////////////////////////
		// ////////////////second version of instruction execution - dealing
		// with long values
		// /////////////////////////////////////////////////
		// S(t) instanceof Comp_type1
		Formula stackTop_ofComp_type1 = new Predicate2Ar(((JavaType) new Stack(
				Expression.COUNTER).getType()).getComputationalType(),
				JavaType.COMPUTATIONAL_TYPE_1, PredicateSymbol.EQ);
		// S(t - 1) instanceof Comp_type2
		Formula stackTop_minus1_ofComp_type2 = new Predicate2Ar(
				((JavaType) new Stack(Expression.getCOUNTER_MINUS_1())
						.getType()).getComputationalType(),
				JavaType.COMPUTATIONAL_TYPE_2, PredicateSymbol.EQ);
		Formula condition = Formula.getFormula(stackTop_ofComp_type1,
				stackTop_minus1_ofComp_type2, Connector.AND);

		Formula f2 = (Formula) _normal_Postcondition.copy();
		f2 = (Formula) f2.substitute(Expression.COUNTER, Expression
				.getCOUNTER_PLUS_1());
		f2 = (Formula) f2.substitute(new Stack(Expression.getCOUNTER_PLUS_1()),
				new Stack(Expression.COUNTER));
		f2 = (Formula) f2.substitute(new Stack(Expression.COUNTER), new Stack(
				Expression.getCOUNTER_MINUS_1()));
		f2 = (Formula) f2.substitute(
				new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(
						Expression.COUNTER));

		Formula branch2 = Formula.getFormula(condition, f2, Connector.IMPLIES);
		wp = Formula.getFormula(branch1, branch2, Connector.AND);
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		Stack stackTop_minus_2 = new Stack(Expression.getCOUNTER_MINUS_2());
		// /////////////////////////////////////////
		// ////////////////first version of instruction execution
		// /////////////////////////////////////////////////

		// s (t-1) of comp type 1
		Predicate2Ar stack_top_of_comp_type_1 = new Predicate2Ar(
				((JavaType) new Stack(Expression.COUNTER).getType())
						.getComputationalType(), JavaType.COMPUTATIONAL_TYPE_1,
				PredicateSymbol.EQ);
		// s (t-1) of_comp_type_1
		Predicate2Ar stack_top_min_1_of_comp_type_1 = new Predicate2Ar(
				((JavaType) new Stack(Expression.getCOUNTER_MINUS_1())
						.getType()).getComputationalType(),
				JavaType.COMPUTATIONAL_TYPE_1, PredicateSymbol.EQ);

		// psi^n[t <-- t+1][S(t+1) <-- S(t)][S(t)<-- S(t-1)][S(t-1) <-- S(t -2
		// )][S(t-2) <-- S(t )]
		VCGPath f1 = (VCGPath) vcs.copy();
		f1.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_1());
		f1.substitute(new Stack(Expression.getCOUNTER_PLUS_1()), new Stack(
				Expression.COUNTER));
		f1.substitute(new Stack(Expression.COUNTER), new Stack(Expression
				.getCOUNTER_MINUS_1()));
		f1.substitute(new Stack(Expression.getCOUNTER_MINUS_1()),
				stackTop_minus_2);
		f1.substitute(stackTop_minus_2, new Stack(Expression.COUNTER));

		// (S(t-2), S(t - 1), S(t) instanceof CompType1) == > psi^n[t <--
		// t+1][S(t+1) <-- S(t)][S(t)<-- S(t-1)][S(t-1) <-- S(t -2 )][S(t-2) <--
		// S(t )]
		Integer key1 = f1.addHyp(getPosition(), stack_top_of_comp_type_1);
		f1.addHypsToVCs(key1);

		Integer key2 = f1.addHyp(getPosition(), stack_top_min_1_of_comp_type_1);
		f1.addHypsToVCs(key2);

		// /////////////////////////////////////////
		// ////////////////second version of instruction execution - dealing
		// with long values
		// /////////////////////////////////////////////////
		// S(t) instanceof Comp_type1
		Formula stackTop_ofComp_type1 = new Predicate2Ar(((JavaType) new Stack(
				Expression.COUNTER).getType()).getComputationalType(),
				JavaType.COMPUTATIONAL_TYPE_1, PredicateSymbol.EQ);
		// S(t - 1) instanceof Comp_type2
		Formula stackTop_minus1_ofComp_type2 = new Predicate2Ar(
				((JavaType) new Stack(Expression.getCOUNTER_MINUS_1())
						.getType()).getComputationalType(),
				JavaType.COMPUTATIONAL_TYPE_2, PredicateSymbol.EQ);

		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_1());
		vcs.substitute(new Stack(Expression.getCOUNTER_PLUS_1()), new Stack(
				Expression.COUNTER));
		vcs.substitute(new Stack(Expression.COUNTER), new Stack(Expression
				.getCOUNTER_MINUS_1()));
		vcs.substitute(new Stack(Expression.getCOUNTER_MINUS_1()), new Stack(
				Expression.COUNTER));

		Integer key3 = vcs.addHyp(getPosition(), stackTop_ofComp_type1);
		vcs.addHypsToVCs(key3);

		Integer key4 = vcs.addHyp(getPosition(), stackTop_minus1_ofComp_type2);
		vcs.addHypsToVCs(key4);

		vcs.merge(f1);
		return vcs;
	}

}
