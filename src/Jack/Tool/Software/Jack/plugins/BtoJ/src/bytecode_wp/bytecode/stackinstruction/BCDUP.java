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
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.formula.Formula;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 *
 * Operation:  Duplicate the top operand stack value
 * 
 * Format : dup 	
 * 
 * Operand Stack : ..., value  == >..., value, value
 * 
 * Description : Duplicate the top value on the operand stack and push the duplicated value onto the operand stack. 
 *  
 * wp = psi^n[t <-- t +1] [S(t+1) <-- S(t) ]
 */
public class BCDUP extends BCInstruction implements BCStackInstruction {

	/**
	 * @param _instruction
	 */
	public BCDUP(InstructionHandle _instruction) {
		super(_instruction);
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(IJml2bConfiguration config, Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		wp = (Formula)_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_1());

//		Predicate2Ar top_stack_eq_top_stack_minus_1 = new Predicate2Ar(new Stack(Expression.COUNTER) , new Stack(Expression.getCOUNTER_PLUS_1()), PredicateSymbol.EQ );
//		wp = Formula.getFormula( wp, top_stack_eq_top_stack_minus_1, Connector.AND);
//		
		Stack topStack = new Stack(Expression.COUNTER);
		Stack topStack_plus_1 = new Stack(Expression.getCOUNTER_PLUS_1());
		wp = (Formula)wp.substitute(topStack_plus_1, topStack);
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
	
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_PLUS_1());


		Stack topStack = new Stack(Expression.COUNTER);
		Stack topStack_plus_1 = new Stack(Expression.getCOUNTER_PLUS_1());
		vcs.substitute(  topStack_plus_1, topStack);
		return vcs;
	}
	

}
