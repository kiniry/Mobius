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
import utils.Util;


/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Trace {
	private BCInstruction[] bytecode ;
	protected Vector  entryBlocks;
	protected Vector exitBlocks;
	
	protected Vector wp;
	
	public Trace(BCInstruction[] _bytecode) {
		bytecode = _bytecode;
		//method = m;
		initGraph();
		setTargetBlocks(bytecode);
	}
	
	/**
	 * set the entry blocks for this method 
	 * (they may be several as there can be 
	 * a loop in the beginning of the method) 
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
				((BCJumpInstruction)code[i]).setTargetBlocks();
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
