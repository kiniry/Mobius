/*
 * Created on Mar 2, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.block;

import java.util.Enumeration;
import java.util.Vector;

import org.apache.bcel.generic.MethodGen;

import formula.Formula;

import bcclass.attributes.ExceptionHandler;
import bcexpression.javatype.JavaReferenceType;
import bytecode.*;
import bytecode.BCExceptionThrower;
import bytecode.BCInstruction;
import bytecode.branch.*;
import utils.Util;


/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Trace {
	private     BCInstruction[] bytecode ;
	//protected Vector  entryBlocks;
	protected Vector exitBlocks;
	
	protected Vector blocks;
	protected Vector wp;
	
	public Trace(BCInstruction[] _bytecode, ExceptionHandler[] _excHandlers) {
		bytecode = _bytecode;
		initGraph();
		
		//sets the blocks that are targets 
		setTargetBlocks(bytecode);
	
		dumpBlocks();
		//sets the exception handlers for instructions that may throw exceptions
		//setExceptionTargetBlocks(bytecode, _excHandlers);
	}
	
	
	/**
	 * 
	 */
	void dumpBlocks() {
		 if (blocks == null) {
		 	Util.dump("not implemented");
		 	return ;
		 }
		
		 
		 Util.dump(" **************** in dumpBlocks ************");	
		 for ( int i = 0; i < blocks.size(); i++) {
			 Block b = (Block)blocks.elementAt(i);
			 b.dump("");
		 }
		 
		 
	}


	/**
	 * set the entry blocks for this method 
	 * (they may be several , for example  there may be 
	 * a loop in the beginning of the method - (2 entry blocks - the loop one and the straight one )) 
	 *
	 */
	public void initGraph(){
		BCInstruction _i = bytecode[0];
		Block _b = null;
		
		while (_i != null)  {
			if ( (_i instanceof BCConditionalBranch) || (_i instanceof BCGOTO)  ) {
				int targetPosition = ((BCJumpInstruction ) _i).getTargetPosition();
				if ( targetPosition == bytecode[0].getPosition()) {
					_b = new LoopBlock(bytecode[0], (BCJumpInstruction)_i ); 
					addBlock(_b);
					return;
				}
			}
			
			if ( _i instanceof EndBlockInstruction ) {
				_b = new Block(bytecode[0],  _i); 
				addBlock(_b);
				/*Util.dump("entry block");
				_b.dump("");*/
				return;
			}	
			_i = _i.getNext();
		}
	}
	
	public void setTargetBlocks(BCInstruction[] code) {	
		for (int i = 0; i < code.length; i++) {
			if (code[i] instanceof BCJumpInstruction) {
				/*Util.dump( " targets for " +  code[i].getInstructionHandle().toString() );*/
				((BCJumpInstruction)code[i]).setTargetBlock(this);
				
				((BCJumpInstruction)code[i]).getTargetBlock().dump("");
				/*Util.dump("===============================");*/
			}
		}
	}
	
/*	*//**
	 * sets the blocks that represent the exception handles 
	 * @param code
	 *//*
	public void setExceptionTargetBlocks(BCInstruction[] code, ExceptionHandler[] handlers) {	
		BCExceptionThrower _excThrower ;  
			for (int i = 0; i < code.length; i++) {
				
				if (code[i] instanceof BCExceptionThrower) {
					Util.dump( " exception handles for " +  code[i].getInstructionHandle().toString() );
					_excThrower  = (BCExceptionThrower)code[i];
					JavaReferenceType[] _excs = _excThrower.getExceptions();
					for (int k = 0; k < _excs.length; k++) { 
						BCInstruction _start =	Util.getExceptionHandlerStarts( _excThrower, _excs[k], handlers , code );
						_excThrower.setExceptionHandlerForException(this, _start, _excs[k]);
					}
					//test
					if (_excThrower.getExceptionHandlerBlocks() == null) {
						Util.dump( " no exception handlers ") ;
					} else {
						Util.dump( " exception handlers  are ") ;
						Block[] blocks = _excThrower.getExceptionHandlerBlocks();
						for (int k = 0; k < blocks.length; k++) {
							blocks[k].dump("");
						}
					}
					Util.dump("===============================");
				}
			}
		}*/
	
	
	/**
	 * gets the block starting at _first and ending at _last from the blocks that are already created
	 * @param _first 
	 * @param _last
	 * @return
	 */
	public Block getBlockStartingAtEndingAt(BCInstruction _first, BCInstruction _last)  {
		if (blocks == null) {
			return null;
		}
		if (blocks.size() == 0) {
			return null;
		}
		Block _b = null;
	/*	Util.dump("block size " + blocks.size());*/
		for ( int  i = 0; i < blocks.size(); i++) {
			_b = (Block)(blocks.elementAt(i));
/*			if(_b == null) {
				Util.dump(" block at position " + i +" is null" );
			} else {
				Util.dump(" block at position " + i + " is ");
				_b.dump("");
			}*/
			if ((_b.getFirst().equals(_first) ) && (_b.getLast().equals( _last) )) {
				return _b;
			}
		}
		return null;
	}
	
	public void addBlock(Block _b) {
		if (blocks  == null) {
			blocks = new Vector();
		}
		blocks.add(_b);
	}
	
	public void dump() {
		Enumeration en = blocks.elements();
		Block b = null;
		while(en.hasMoreElements()) {
			b = (Block)(en.nextElement());
			b.dump("");
		}
	}
	
	public Vector getEntryBlocks() {
		return blocks;
	}
	
	public Vector getExitBlocks() {
		return exitBlocks;
	}
	
/*	private void addEntryBlock(Block _block) {
		if (blocks == null ){
			blocks = new Vector();	
		}
		blocks.add(_block);
	}*/
	
	public Formula wp() {
		//for (int i = 0 ; i < bytecode.length; i++) {
		//	if (bytecode[i] instanceof ExitInstruction ) {
				
		//	}
		//}
		return null;
	}
	
}
