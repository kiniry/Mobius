package bytecode;

import java.util.HashMap;
import java.util.Iterator;

import org.apache.bcel.generic.ExceptionThrower;
import org.apache.bcel.generic.InstructionHandle;

import formula.Formula;

import specification.ExceptionalPostcondition;
import utils.FreshIntGenerator;
import utils.Util;

import bcexpression.EXCEPTIONVariable;
import bcexpression.heap.Reference;
import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;

/**
 * @author M. Pavlova
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public  abstract class BCExceptionThrower extends BCUnconditionalBranch {	

	/**
	 * mapping between an exception and aninstruction where the handler for this exception starts
	 */
	private HashMap exception_targetBlock;
	
	
	
	/**
	 * @param _instruction
	 */
	public BCExceptionThrower(InstructionHandle _instruction) {
		super(_instruction);
		setThrownExceptions(_instruction);
		// TODO Auto-generated constructor stub
	}
	
	/**
	 * sets the exceptions that the instriuction may throw
	 * @param _instruction
	 */
	private void setThrownExceptions(InstructionHandle  _instruction)  {	
		Class[] _exceptions = ((ExceptionThrower)_instruction.getInstruction()).getExceptions();
		if (_exceptions == null || _exceptions.length == 0 ){
			return;
		}
		exception_targetBlock = new HashMap();
		for (int i = 0; i < _exceptions.length; i++) {
			exception_targetBlock.put( JavaType.getJavaClass(_exceptions[i].getName()), null );
		}
	}
	
	/**
	 * this method sets the block that represents the exception handler for the <code>_exc </code> given as parameter
	 * starting at <code>_startExcHandler</code> instruction
	 * The method is called from outside, once the trace of this method is initialised.
	 * @param _trace
	 */
	public void setExceptionHandlerForException(Trace _trace, BCInstruction _startExcHandler, JavaReferenceType _exc )  {
		BCInstruction _last = _startExcHandler;
		Block _b = null;	
		while (_last != null)  {
			if ((_last instanceof BCConditionalBranch) || (_last instanceof EndBlock ) ) {
				if ((_b = _trace.getBlockStartingAtEndingAt(_startExcHandler, _last)) == null ){
					_b = Util.getBlock(_startExcHandler,  _last);
					_trace.addBlock(_b);
				} 
				if (_b != null) {
					_b.dump(""); 
					exception_targetBlock.put(_exc, _b);
					break;
				}
			}
			_last = _last.getNext();		
		}
		if ((_b != null ) && (_b instanceof LoopBlock ) ) {
			return;
		}
		while (_last != null)  {
			if ( (_last instanceof BCJumpInstruction) && (_startExcHandler.equals(((BCJumpInstruction)_last).getTarget())) ){
				if ((_b = _trace.getBlockStartingAtEndingAt(_startExcHandler, _last)) == null ){
					_b = Util.getBlock(_startExcHandler,  (BCJumpInstruction)_last);
					_trace.addBlock(_b);
				} 
				_b.dump("");
				exception_targetBlock.put(_exc, _b);
				return;	
			}
			_last = _last.getNext();
		}	
	}
	

	/** 
	 * @param _exc_type
	 * @return the block that  represents the exception handle for the 
	 */
	public Block getExceptionHandleBlockForException(JavaReferenceType _exc_type) {
		if (exception_targetBlock == null){
			return null;
		}
		if (exception_targetBlock.size() <= 0){
			return null;
		}
		Block _b = (Block)exception_targetBlock.get(_exc_type);  
		return _b;
	}
		
	public JavaReferenceType[] getExceptions() {
		if ( exception_targetBlock == null) {
			return null;
		}
		Iterator _excSet = exception_targetBlock.keySet().iterator();
		JavaReferenceType[] _excArr = new JavaReferenceType[exception_targetBlock.size()]; 
		int i  =  0;
		while (_excSet.hasNext() ) {
			_excArr[i] = (JavaReferenceType)_excSet.next();  
		}
		return _excArr;
	}

	/* *
	 * the method returns the postcondition that must  be valid 
	 * after this instruction throws an exception of type _exc_type
	 * @see bytecode.ByteCode#wp(formula.Formula, specification.ExceptionalPostcondition)
	 */
	public Formula getWpForException(JavaReferenceType _exc_type, ExceptionalPostcondition _exc_post)  {
		Block block = (Block)exception_targetBlock.get(_exc_type);
		Formula _exc_termination;
		// in case there is no handler for this exception the specified exceptional posctondition must be taken into account
		if ( block == null ) {
			_exc_termination  =  _exc_post.getExcPostconditionFor(_exc_type);
			Formula _exc_termination_copy = _exc_termination.copy();
			_exc_termination_copy.substitute(new EXCEPTIONVariable(FreshIntGenerator.getInt(), _exc_type), new Reference(FreshIntGenerator.getInt(), _exc_type) );
			return _exc_termination_copy;
		}
		//else if there is a handle then the wp of this handler must be taken
		_exc_termination = block.getWp();
		return _exc_termination;
	}
}
