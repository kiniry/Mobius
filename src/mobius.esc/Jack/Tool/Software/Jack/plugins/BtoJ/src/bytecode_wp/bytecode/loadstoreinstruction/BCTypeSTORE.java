/*
 * Created on Apr 5, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bytecode.loadstoreinstruction;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.InstructionHandle;


import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcexpression.BCLocalVariable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.formula.Formula;
import bytecode_wp.utils.Util;
import bytecode_wp.vcg.VCGPath;


/**
 * @author mpavlova
 *
 * Operation: Store the stack top  into local variable
 * 
 * Format : astore index 	
 * 
 * Operand Stack:   ..., objectref ==> ...
 * 
 * wp = psi^n[t < -- t -1 ][local(index)  <-- S( t)] 
 */
public class BCTypeSTORE extends BCLocalVariableInstruction {
	//ASTORE, ISTORE, LSTORE
	
	/**
	 * @param _instruction
	 */
	public BCTypeSTORE(InstructionHandle _instruction, BCLocalVariable _lv) {
		super(_instruction, _lv);
		setType((JavaType)_lv.getType());
	}

	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula wp(
		IJml2bConfiguration config,
		Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		Formula wp;
		
		wp = (Formula)_normal_Postcondition.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		wp = (Formula)wp.substitute(getLocalVariable(),  new Stack(Expression.COUNTER) );
		return wp;
	}

	public VCGPath wp(IJml2bConfiguration config, VCGPath vcs, ExsuresTable _exc) {
		vcs.substitute(Expression.COUNTER, Expression.getCOUNTER_MINUS_1());
		vcs.substitute(getLocalVariable(),  new Stack(Expression.COUNTER) );
		return vcs;
	}
}
