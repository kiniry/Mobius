/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package utils;

import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.GotoInstruction;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.CodeExceptionGen;
import org.apache.bcel.generic.IfInstruction;
import org.apache.bcel.generic.JsrInstruction;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.RET;
import org.apache.bcel.generic.ReturnInstruction;
import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import bcexpression.type.JavaObjectType;
import bcexpression.type.JavaType;
import bcexpression.type.JavaTypeFactory;
import bytecode.BCAthrowInstruction;
import bytecode.BCConditionalBranch;
import bytecode.BCGotoInstruction;
import bytecode.BCInstruction;
import bytecode.BCJsrInstruction;
import bytecode.BCJumpInstruction;
import bytecode.BCRetInstruction;
import bytecode.BCReturnInstruction;
import bytecode.Block;
import bytecode.EndBlock;
import bytecode.LoopBlock;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Util {
	public static boolean DUMP = true;
	
	
	public static BCInstruction[] wrapByteCode(InstructionList _il , MethodGen _mg ) {
		InstructionHandle[] _iharr =  _il.getInstructionHandles(); 
		BCInstruction[] _bc = new BCInstruction[_iharr.length];
		for  (int i = 0; i < _iharr.length; i++) {
			 if  (_iharr[i].getInstruction() instanceof ReturnInstruction) {
				_bc[i]  = new BCReturnInstruction(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof  RET) {
				_bc[i] = new BCRetInstruction(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof  GotoInstruction) {
				_bc[i] = new BCGotoInstruction(_iharr[i]);
			} else if  (_iharr[i].getInstruction() instanceof ATHROW) {
				_bc[i] = new BCAthrowInstruction(_iharr[i]);	
			} else if (_iharr[i].getInstruction() instanceof  JsrInstruction) {
				_bc[i] = new BCJsrInstruction(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof IfInstruction ){
				_bc[i] = new BCConditionalBranch(_iharr[i]);
			 } else {
				_bc[i] = new BCInstruction(_iharr[i]);
			}
			_bc[i].setBCIndex(i);
			//set the bytecode command at the previous position and at the next positition
			if (i > 0) {
				_bc[i].setPrev(_bc[ i-1]);
				_bc[i-1].setNext(_bc[i]);
			}
		} 
		_bc = setTargets(_bc, _mg);
		return _bc;
	}
	
	private static BCInstruction[] setTargets(BCInstruction[] _bc, MethodGen _mg) {
//		set theTarget
		for (int i = 0; i < _bc.length; i++) {
			if (_bc[i] instanceof BCJumpInstruction) {
				BCInstruction _ih = null;	
				int offset;
				//dumps the jump instruction
				Instruction _i = _bc[i].getInstructionHandle().getInstruction();
				Util.dump(" setTargets for " + _bc[i].getInstructionHandle().toString());
				
				if ((_bc[i] instanceof  BCAthrowInstruction) )  {
					InstructionHandle  _ins = null;
					if ( (_ins = getExceptionHandler((BCAthrowInstruction)_bc[i], _mg)) == null ) {
						continue;
					}
					offset = _ins.getPosition();
					//Util.dump(((BCAthrowInstruction)_bc[i]).getExceptions()[0].toString());
				} else {
					offset = ((BranchInstruction)_i).getTarget().getPosition();
				}
				_ih = getBCInstructionAtPosition(_bc,  offset);
				((BCJumpInstruction)_bc[i]).setTarget(_ih );
				_ih.addTargeter(_bc[i]);
				
			}
		}
		return _bc;
	}
	
	/**
	 * @param instruction
	 * @return
	 */
	private static InstructionHandle getExceptionHandler(BCAthrowInstruction _instr, MethodGen mg) {
		// TODO Auto-generated method stub
		CodeExceptionGen[] _ehs = mg.getExceptionHandlers();
		
		for (int i = 0; i < _ehs.length; i++) {
			
			if ( ( _ehs[i].getStartPC().getPosition() < _instr.getPosition() ) &&  (_ehs[i].getEndPC().getPosition() > _instr.getPosition() ) ) {
				JavaType _ot =  JavaTypeFactory.getJavaTypeFactory().getJavaType(_ehs[i].getCatchType());
				JavaType[] _e = _instr.getExceptions();
				
				//handles any kind of exception
				if  ((_ot == null) ||( ((JavaObjectType)_e[0]).subclassOf((JavaObjectType)_ot) )) {
					//Util.dump("handler " + _ehs[i].getHandlerPC().toString());
					return _ehs[i].getHandlerPC();
				}
			}
		}
		return null;
	}
	
	/**
	 * @param i
	 * @return the 
	 */
	private static BCInstruction getBCInstructionAtPosition(BCInstruction[] _b, int offset)  {
	 	for( int i = 0; i < _b.length; i++)  {
	 		if (_b[i].getPosition() == offset ) {
	 			return _b[i];  
	 		} 
	 	}
		return null;
	}

	private static LoopBlock getLoopBlock(BCInstruction _first , BCInstruction _last) {
		LoopBlock _lb = null ;
		if (  ((_last instanceof BCConditionalBranch ) || (_last instanceof BCGotoInstruction )) && 
		  (((BCJumpInstruction)_last).getTarget().getInstructionHandle().equals( _first.getInstructionHandle()))) {
			_lb = new LoopBlock(_first, (BCJumpInstruction)_last);
		}
		return _lb;
	}
	
	public static  Block getBlock(BCInstruction _first , BCInstruction _last) {
		Block _b = null;
		//Util.dump("exception trace: " + _last.getInstructionHandle().toString() );
		_b = getLoopBlock(_first, _last);
		if (_b != null) {
			return _b;
		}
		// test was if ( (_last instanceof BCUnconditionalBranch) || (_last instanceof BCReturnInstruction)), as jsr instruction doesnot delimit a block- it detremines a jump to another block 
		if ( _last instanceof EndBlock) {
			_b = new Block(_first, _last );
		}
		
		return _b;
	}
	
	/**
	 * looks for loop starting with _first and end with _last or an instruction which is next to the _last
	 * @param _first - loop initial instruction
	 * @param _last - instruction that wiol be th end ogf the loop or the end of the loop will be next to the _last instruction 
	 * @return loop that starts at 
	 */
	public static LoopBlock searchLoopStartingAt(BCInstruction _first, BCInstruction _last) {
		LoopBlock _b = null;
		while(_last != null) {
			if ( (_last instanceof BCJumpInstruction ) &&  ((BCJumpInstruction)_last).getTarget().getInstructionHandle().equals( _first.getInstructionHandle())) {	 
					_b = getLoopBlock(_first , _last );			
			}
			_last = _last.getNext();
		}
		return _b;
	}
	
	/*public static Vector getBlocks(BCInstruction[] _is) {
		Vector _b = null;
		for (int i = 0; i < _is.length; i++)  {
			if (i ==0)  {
				Vector  _v = getBlocksStartingAt(_is[i]);
				if (_v == null)  {
					continue;
				}
				if  (_b == null) {
					_b = new Vector();
				}
				_b.addAll(_v);
			}
			if (  _is[i].getTargeters() != null ) {
				Vector  _v = getBlocksStartingAt(_is[i] ) ;
				if (_v == null)  {
					continue;
				}
				if  (_b == null) {
					_b = new Vector();
				}
				_b.addAll(_v);
			}
		}
		return _b;
	}
*/
	
	 
	
	public static void dump(String s) {
		if (DUMP) {
			System.out.println(s);
		}
	}
}
