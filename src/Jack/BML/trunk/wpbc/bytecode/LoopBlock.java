/*
 * Created on Feb 24, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import java.util.Vector;

import org.apache.bcel.generic.ConstantPoolGen;

import vm.Stack;

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
	
	public Formula wp(Formula _normal_Postcondition, Formula _exc_Postcondition ,Stack stack, ConstantPoolGen _cp) {
		if (wp != null) {
			return wp;
		}
		Formula _np = new Formula( _normal_Postcondition,  getInvariant(), Connector.AND );	
		wp = super.wp(_np,_exc_Postcondition, stack,   _cp);
		return wp; 
	}
	
	public void dump(String _offset) {
		String offset = "       ";
		System.out.println(_offset + "LoopBlock( ");
				System.out.println(_offset + offset +"fst: " + getFirst().getPosition() + " "+ getFirst().getInstructionHandle().getInstruction().toString()); 
//				Vector j ;
//				if (jumps != null )  {
//					for (int i = 0; i < jumps.size(); i++ ){
//						j =(Vector)(jumps.elementAt(i));
//						BCJumpInstruction jmp = (BCJumpInstruction) ( j.elementAt(0) );
//						Block block = (Block)( j.elementAt(1) );
//						System.out.println( _offset +  offset  +"jmp:"+  jmp.getOffset() +" "+ jmp.getInstructionHandle().getInstruction().toString() );
//						block.dump(_offset +  offset ) ;
//					}
//				}
				System.out.println(  _offset + offset +"end: "+  getLast().getPosition() + " "+ getLast().getInstructionHandle().getInstruction().toString() );
				System.out.println( _offset +")"); 
	}
}
