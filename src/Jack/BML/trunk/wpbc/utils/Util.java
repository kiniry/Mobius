/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package utils;

import java.util.Vector;

import org.apache.bcel.generic.AALOAD;
import org.apache.bcel.generic.AASTORE;
import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.ArithmeticInstruction;
import org.apache.bcel.generic.ArrayInstruction;
import org.apache.bcel.generic.BALOAD;
import org.apache.bcel.generic.BASTORE;
import org.apache.bcel.generic.CALOAD;
import org.apache.bcel.generic.CASTORE;
import org.apache.bcel.generic.CPInstruction;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.ConstantPushInstruction;
import org.apache.bcel.generic.ConversionInstruction;
import org.apache.bcel.generic.DALOAD;
import org.apache.bcel.generic.DASTORE;
import org.apache.bcel.generic.ExceptionThrower;
import org.apache.bcel.generic.FALOAD;
import org.apache.bcel.generic.FASTORE;
import org.apache.bcel.generic.GotoInstruction;
import org.apache.bcel.generic.IALOAD;
import org.apache.bcel.generic.IASTORE;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.CodeExceptionGen;
import org.apache.bcel.generic.IfInstruction;
import org.apache.bcel.generic.JsrInstruction;
import org.apache.bcel.generic.LALOAD;
import org.apache.bcel.generic.LASTORE;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.RET;
import org.apache.bcel.generic.ReturnInstruction;
import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.SALOAD;
import org.apache.bcel.generic.SASTORE;
import org.apache.bcel.generic.StackInstruction;
import org.apache.bcel.generic.Type;
import org.apache.bcel.generic.TypedInstruction;

import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;

import bytecode.BCATHROW;
import bytecode.BCArithmeticInstructionWithException;
import bytecode.BCAritmeticInstruction;
import bytecode.BCCPInstruction;
import bytecode.BCConditionalBranch;
import bytecode.BCConstantPUSHInstruction;
import bytecode.BCConversionInstruction;
import bytecode.BCExceptionThrower;
import bytecode.BCGOTO;
import bytecode.BCInstruction;
import bytecode.BCJSR;
import bytecode.BCJumpInstruction;
import bytecode.BCRET;
import bytecode.BCStackInstruction;
import bytecode.BCTypeALOAD;
import bytecode.BCTypeRETURN;
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
	
	
	public static BCInstruction[] wrapByteCode(InstructionList _il , MethodGen _mg,  ConstantPoolGen _cp ) {
		InstructionHandle[] _iharr =  _il.getInstructionHandles(); 
		BCInstruction[] _bc = new BCInstruction[_iharr.length];
		for  (int i = 0; i < _iharr.length; i++) {
			 if  (_iharr[i].getInstruction() instanceof ReturnInstruction) {
				_bc[i]  = new BCTypeRETURN(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof  RET) {
				_bc[i] = new BCRET(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof  GotoInstruction) {
				_bc[i] = new BCGOTO(_iharr[i]);
			} else if  (_iharr[i].getInstruction() instanceof ATHROW) {
				_bc[i] = new BCATHROW(_iharr[i]);	
			} else if (_iharr[i].getInstruction() instanceof  JsrInstruction) {
				_bc[i] = new BCJSR(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof IfInstruction ){
				_bc[i] = new BCConditionalBranch(_iharr[i]);
			 }  else if ((_iharr[i].getInstruction() instanceof  ArithmeticInstruction) && ( _iharr[i].getInstruction() instanceof  ExceptionThrower) ) {
				_bc[i] = new  BCArithmeticInstructionWithException(_iharr[i]);
			}  else if (_iharr[i].getInstruction() instanceof  ArithmeticInstruction) {
				_bc[i] = new  BCAritmeticInstruction(_iharr[i]);
			}  else if (_iharr[i].getInstruction() instanceof  ConstantPushInstruction) {
				_bc[i] = new BCConstantPUSHInstruction(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof ConversionInstruction ) {
				_bc[i] = new BCConversionInstruction(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof   StackInstruction) {
				_bc[i] = new BCStackInstruction(_iharr[i]);
			} else if (_iharr[i].getInstruction() instanceof  ArrayInstruction ) {
				JavaType  _type =JavaType.getJavaClass(((TypedInstruction)_iharr[i].getInstruction()).getType(_cp).getSignature() ); 
				if ( (_iharr[i].getInstruction() instanceof AALOAD) ||  (_iharr[i].getInstruction() instanceof BALOAD ) || (_iharr[i].getInstruction() instanceof CALOAD ) || 
					 (_iharr[i].getInstruction() instanceof LALOAD  ) || (_iharr[i].getInstruction() instanceof DALOAD) ||  (_iharr[i].getInstruction() instanceof FALOAD ) || 
					 (_iharr[i].getInstruction() instanceof SALOAD ) || (_iharr[i].getInstruction() instanceof IALOAD )) {
					_bc[i] =new  BCTypeALOAD(_iharr[i], _type );
				}  
				if ((_iharr[i].getInstruction() instanceof AASTORE) || ( _iharr[i].getInstruction() instanceof BASTORE) || (_iharr[i].getInstruction() instanceof CASTORE) ||
				    (_iharr[i].getInstruction() instanceof LASTORE)   || (_iharr[i].getInstruction() instanceof DASTORE)  || (_iharr[i].getInstruction() instanceof FASTORE) ||
				    (_iharr[i].getInstruction() instanceof SASTORE)   || (_iharr[i].getInstruction() instanceof IASTORE)) {
					_bc[i] = new  BCTypeALOAD(_iharr[i], _type); 
				}
			} else if (_iharr[i].getInstruction() instanceof  CPInstruction ) {
				_bc[i] = new BCCPInstruction(_iharr[i]);
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
		
		//set possible next instructions  for jump instructions - 
		
		for (int i = 0; i < _bc.length; i++) {
//			if ( _bc[i] instanceof BCExceptionThrower ) {	
//				((BCExceptionThrower)_bc[i]).setExceptionTarget( getExceptionHandlerStarts((BCExceptionThrower)_bc[i], _mg, _bc) );
//			}
			if (_bc[i] instanceof BCJumpInstruction) {
				BCInstruction _ih = null;	
				int offset;
				//dumps the jump instruction

				Util.dump(" setTargets for " + _bc[i].getInstructionHandle().toString());
				offset = ( (BCJumpInstruction)_bc[i]).getTargetPosition();
				_ih = getBCInstructionAtPosition(_bc,  offset);
				((BCJumpInstruction)_bc[i]).setTarget(_ih );
				_ih.addTargeter(_bc[i]);
				
			}
		}
		return _bc;
	}
	
	/**
	 * this method finds the instruction at which the exception handler for the
	 * exception Thrower instruction given as parameter  starts.
	 * @param instruction- the instrructiuon for whioch an exception handler is searched
	 * @return  the instruction which is the start for the block that represents the instruction handle
	 */
	public static BCInstruction getExceptionHandlerStarts(BCExceptionThrower _instr, JavaReferenceType _exc ,MethodGen mg, BCInstruction[] _bc) {
	
		CodeExceptionGen[] _excHandles = mg.getExceptionHandlers();
		BCInstruction _i = null;
		for (int i = 0; i < _excHandles.length; i++)  {	
			if ( ( _excHandles[i].getStartPC().getPosition() < _instr.getPosition() ) &&  (_excHandles[i].getEndPC().getPosition() > _instr.getPosition() ) ) {
				//getCatchType() returns null for if any exception may be managed by this handle
				JavaType _ot =  new JavaObjectType(_excHandles[i].getCatchType());
				if  ((_ot == null) ||( ((JavaObjectType)_exc).subclassOf((JavaObjectType)_ot) )) {
					//Util.dump("handler " + _ehs[i].getHandlerPC().toString());
					_i = getBCInstructionAtPosition( _bc ,  _excHandles[i].getHandlerPC().getPosition());
				}
			}
		}
		return  _i;
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
		if (  ((_last instanceof BCConditionalBranch ) || (_last instanceof BCGOTO )) && 
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
