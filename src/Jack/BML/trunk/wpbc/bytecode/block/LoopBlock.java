/*
 * Created on Feb 24, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.block;

import java.util.HashMap;
import java.util.Vector;

import org.apache.bcel.generic.ConstantPoolGen;


import bcclass.attributes.ExsuresTable;
import bcexpression.vm.Stack;
import bytecode.BCInstruction;
import bytecode.branch.BCJumpInstruction;

import formula.Connector;
import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class LoopBlock  extends Block {
	private Formula invariant;
	//private Vector wps;

	/**
	 * @param _first
	 */
	public LoopBlock(BCInstruction _first, BCJumpInstruction _last) {
		super(_first, _last);
	}

	/**
	 * 
	 * @param _invariant
	 */	
	public void setInvariant(Formula _invariant) {
		invariant = _invariant;
	}
	
	public Formula  getInvariant() {
		return invariant;
	}
	
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition ) {
//		if (wp != null) {
//			return wp;
//		}
		Formula _np = Formula.getFormula( _normal_Postcondition,  getInvariant(), Connector.AND );	
		Formula wp = super.wp(_np,_exc_Postcondition);
		return wp; 
	}
	
	public void dump(String _offset) {
		String offset = "       ";
		System.out.println(_offset + " LoopBlock( ");
				System.out.println(_offset + offset +"fst: " + getFirst().getPosition() + " "+ getFirst().getInstructionHandle().getInstruction().toString()); 
				System.out.println(  _offset + offset +"end: "+  getLast().getPosition() + " "+ getLast().getInstructionHandle().getInstruction().toString() );
				System.out.println( _offset +")"); 
	}
}
