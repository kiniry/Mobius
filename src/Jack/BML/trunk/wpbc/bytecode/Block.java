/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import java.util.Vector;

import org.apache.bcel.generic.ConstantPoolGen;

import utils.Util;
import vm.Stack;
import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
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
	
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula)
	 */
	public Formula wp(Formula _normal_Postcondition, Formula _exc_Postcondition, Stack stack, ConstantPoolGen _cp ) {
		if (wp != null) {
			return wp;
		}
		//wps = new Vector();
		BCInstruction _instr = last;
		Formula  _np = _normal_Postcondition; 
		Formula _ep = _exc_Postcondition;
		while (! _instr.equals(first)) {
			_np = _instr.wp(_normal_Postcondition, _exc_Postcondition, stack, _cp);
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



}
