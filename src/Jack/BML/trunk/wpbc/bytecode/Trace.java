/*
 * Created on Mar 2, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import java.util.Enumeration;
import java.util.Vector;

import org.apache.bcel.generic.MethodGen;

import bcexpression.javatype.JavaReferenceType;
import utils.Util;


/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Trace {
	private     BCInstruction[] bytecode ;
	protected Vector  entryBlocks;
	protected Vector exitBlocks;
	
	protected Vector blocks;
	
	
	protected Vector wp;
	private MethodGen methodGen;
	
	public Trace(BCInstruction[] _bytecode, MethodGen _methodGen) {
		bytecode = _bytecode;
		methodGen = _methodGen;
		//method = m;
		initGraph();
		
		//sets the blocks that are targets 
		setTargetBlocks(bytecode);
		setExceptionTargetBlocks(bytecode);
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
			if ( _i instanceof EndBlock ) {
				_b = Util.getBlock(bytecode[0],  _i); 
				addEntryBlock(_b);
				Util.dump("entry block");
				_b.dump("");
				break;
			}	
			_i = _i.getNext();
		}
		if (_b instanceof LoopBlock) {
			return;
		}
		while (_i != null)  {
			if ( (_i instanceof BCJumpInstruction) && (bytecode[0].equals(((BCJumpInstruction)_i).getTarget())) ){
					_b = new LoopBlock(bytecode[0],  (BCJumpInstruction)_i); 
					addEntryBlock(_b) ;
					Util.dump("entry block");
					_b.dump("");
					return;	
			}
			_i = _i.getNext();
		}				
	}
	
	public void setTargetBlocks(BCInstruction[] code) {	
		for (int i = 0; i < code.length; i++) {
			if (code[i] instanceof BCJumpInstruction) {
				Util.dump( " targets for " +  code[i].getInstructionHandle().toString() );
				((BCJumpInstruction)code[i]).setTargetBlocks(this);
				
				//test
				if (((BCJumpInstruction)code[i]).getTargetBlocks() == null) {
					Util.dump( " number targets null") ;
				} else {
					Util.dump( " number targets " + ((BCJumpInstruction)code[i]).getTargetBlocks().size() ) ;
				}
				Util.dump("===============================");
			}
		}
	}
	
	/**
	 * sets the blocks that represent the exception handles 
	 * @param code
	 */
	public void setExceptionTargetBlocks(BCInstruction[] code) {	
		BCExceptionThrower _excThrower ;  
			for (int i = 0; i < code.length; i++) {
				
				if (code[i] instanceof BCExceptionThrower) {
					Util.dump( " exception handles for " +  code[i].getInstructionHandle().toString() );
					_excThrower  = (BCExceptionThrower)code[i];
					JavaReferenceType[] _excs = _excThrower.getExceptions();
					for (int k = 0; k < _excs.length; k++) { 
						BCInstruction _start =	Util.getExceptionHandlerStarts( _excThrower, _excs[k], methodGen, bytecode );
						_excThrower.setExceptionHandlerForException(this, _start, _excs[k]);
					}
					//test
					if (((BCExceptionThrower)code[i]).getTargetBlocks() == null) {
						Util.dump( " number targets null") ;
					} else {
						Util.dump( " number targets " + ((BCJumpInstruction)code[i]).getTargetBlocks().size() ) ;
					}
					Util.dump("===============================");
				}
			}
		}
	
	
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
		for ( int  i = 0; i < blocks.size(); i++) {
			_b = (Block)(blocks.elementAt(i));
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
		Enumeration en = entryBlocks.elements();
		Block b = null;
		while(en.hasMoreElements()) {
			b = (Block)(en.nextElement());
			b.dump("");
		}
	}
	
	public Vector getEntryBlocks() {
		return entryBlocks;
	}
	
	public Vector getExitBlocks() {
		return exitBlocks;
	}
	
	private void addEntryBlock(Block _block) {
		if (entryBlocks == null ){
			entryBlocks = new Vector();	
		}
		entryBlocks.add(_block);
	}
	
	public void wp() {
		//for (int i = 0 ; i < bytecode.length; i++) {
		//	if (bytecode[i] instanceof ExitInstruction ) {
				
		//	}
		//}
	}
	
}
