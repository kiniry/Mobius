/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.block;

import java.util.HashMap;
import java.util.Vector;

import bcclass.attributes.ExsuresTable;
import bytecode.BCInstruction;
import bytecode.ByteCode;



import utils.Util;

import formula.Formula;

/**
 * @author mpavlova
 *
 * a block is defined by the  rules:
 * 1. if it ends with a jump that jumps beckwards.
 * 
 * 2.1. it starts either with the first instruction of a bytecode
 * either of an instruction that is a target of a jump instruction.
 * 
 * 2.2. it ends with an instruction that is either a goto, athrow, ret or return instruction
 */
public class Block  implements ByteCode {
	private BCInstruction first;
	private BCInstruction last;
	
	protected Vector next;
	protected Vector prev;
	
	private Formula postcondition;
	
	/**
	 * Vector of formulas whose conjunction is the wp of the block 
	 */
	protected Formula wp;
	
	
	public Block(BCInstruction _first, BCInstruction _last  ) {
		setFirst(_first);
		setLast(_last); 
	}
	
	public BCInstruction getFirst() {
		return first;
	}
	
	private void setFirst(BCInstruction _first) {
		first = _first;
	}
	
	private void setLast(BCInstruction _ji){
		last  = _ji;
	}
	
	public BCInstruction getLast() {
		return last;
	}
	
	public void setPostcondition(Formula _postcondition) {
		postcondition = _postcondition;
	}
	
	public Formula getPostcondition() {
		return postcondition;
	}
	
	/**
	 * 
	 * @author mpavlova
	 * deprecated
	 * To change the template for this generated type comment go to
	 * Window>Preferences>Java>Code Generation>Code and Comments
	 */
	public void setNext(Vector _next ) {
		next = _next;
	} 
	
	/**
	 * 
	 * @author mpavlova
	 * deprecated
	 * To change the template for this generated type comment go to
	 * Window>Preferences>Java>Code Generation>Code and Comments
	 */
	public Vector getNext() {
		return next;
	} 

	/**
	 * 
	 * @author mpavlova
	 * deprecated
	 * To change the template for this generated type comment go to
	 * Window>Preferences>Java>Code Generation>Code and Comments
	 */
	public void setPrev(Vector _prev) {
		prev = _prev;
	} 

	/**
	 * 
	 * @author mpavlova
	 * deprecated
	 * To change the template for this generated type comment go to
	 * Window>Preferences>Java>Code Generation>Code and Comments
	 */
	public Vector getPrev() {
		return prev;
	} 
	
	/**
	 * returns the calculated wp for the block
	 * @return <code>wp </code>
	 */
	public Formula  getWp() {
		return wp;
	}
	
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula)
	 */
	public Formula wp(Formula _normal_Postcondition, ExsuresTable _exc_Postcondition) {
		if (wp != null) {
			return wp;
		}
		//wps = new Vector();
		BCInstruction _instr = last;
		Formula  _np = _normal_Postcondition; 
		
		while (! _instr.equals(first)) {
			_np = _instr.wp(_np,  _exc_Postcondition);
			_instr = _instr.getPrev();
		}
		wp = _np;
		return  wp;
		
	}
	
	public void dump(String _offset) {
		if (Util.DUMP) {
		
			String offset = "     ";
			System.out.println(_offset + "Block( ");
			System.out.println(_offset + offset +"fst: "+  " " +first.getPosition()+" "+ first.getInstructionHandle().getInstruction().toString()); 
			
			System.out.println(  _offset + offset +"end: "+  last.getPosition() +" "+ last.getInstructionHandle().getInstruction().toString() );
			System.out.println( _offset +  ")");
			
			BCInstruction _i = first;
		}
	}


	public boolean equals(Block _block) {
		if ((first.equals(_block.getFirst())) && (last.equals(_block.getLast()))) { 
			return true;
		}
		return false;
	} 


}
