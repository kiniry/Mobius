/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;


import java.util.Vector;

import org.apache.bcel.generic.ExceptionThrower;
import org.apache.bcel.generic.InstructionHandle;

import bcexpression.javatype.JavaType;
import formula.Formula;





/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract  class BCInstruction  implements ByteCode{

	private Formula wp;
	
	/**
	 * this field should disappear in the end. Only the needed information extracted from the object should reamain.
	 */
	private InstructionHandle instructionHandle;	
	private BCInstruction prev;
	private BCInstruction next;
	
	/**
	 * a list of instructions that target to this one 
	 */
	private Vector targeters;
	
	//the index at which this instruction  is in the bytecode
	private int position;

	private int index;
	private int offset;
	
	/**
	 * exceptions that this throw instruction may cause
	 */
	private JavaType[] exceptions;
	
	public BCInstruction(InstructionHandle  _instruction)  {
		instructionHandle = _instruction; 
		setPosition(instructionHandle);
	}
	
	public InstructionHandle getInstructionHandle() {
		return instructionHandle;
	}
	
	
	public void setWp(Formula _f) {
		wp = _f;
	}
	
	public Formula getWp() {
		return wp;
	}
	
	public void setNext(BCInstruction _next)  {
		next = _next;
	}
	
	public void setPrev(BCInstruction _prev )  {
		prev = _prev;
	}
	
	public BCInstruction getNext() {
		return next;
	}
	
	public BCInstruction getPrev() {
		return prev;
	}

	/**
	 * @param i - this the index at which 
	 * this command appears in the bytecode array of instruction 
	 */
	public void setBCIndex(int i) {
		index = i;
	}
	
	public int getBCIndex() {
		return index;
	}
	
	/*
	 * @return - the offset of the instruction 
	 * from the beginning 
	 */
	public int getPosition() {
		return position;
	}
	
	private void setPosition(InstructionHandle instructionHandle) {
		position = instructionHandle.getPosition();
	}
	/**
	 * @return
	 */
	public Vector getTargeters() {
		return targeters;
	}

	/**
	 * @param vector
	 */
	public void setTargeters(Vector vector) {
		targeters = vector;
	}
	
	public void addTargeter(BCInstruction _t){
		if  (targeters == null) {
			targeters = new Vector();
		}
		targeters.add(_t);
	} 
	
	
	
	/* (non-Javadoc)
	 * @see bytecode.ByteCode#wp(formula.Formula)
	 */
//	public Formula wp(Formula _n_Postcondition, ExceptionalPostcondition _e_Postcondition );
//	 {
//		if (wp != null) {
//			return wp;
//		}
//		Instruction _instruction = instructionHandle.getInstruction();
//		Vector _subexpr ;
//		
//		if ((_instruction instanceof  ArrayInstruction) && (_instruction instanceof StackProducer)) {
//			wp = wpType_aload(_n_Postcondition, _e_Postcondition);
//			return wp;
//		} else if( (_instruction instanceof  ArrayInstruction) && (_instruction instanceof StackConsumer)) {
//			//TYPE_STORE		
//		
//			return wp;
//		} else if ( _instruction instanceof ACONST_NULL) {
//			return wp;
//		} else if (_instruction instanceof LoadInstruction ) {
//			return wp;
//		}
//		/*else if (_instruction instanceof  ALOAD_N) {
//			
//		}*/
//		else if (_instruction instanceof ANEWARRAY ) {
//			//..., count ==> ..., arrayref
//		 	return wp;
//		} else if(_instruction instanceof ARETURN ) {
//		  	return wp;
//		} else if(_instruction instanceof  ARRAYLENGTH ) {
//		} else if(_instruction instanceof ASTORE ) {
//		  	//..., objectref  ==> ...
//		 	return wp;
//		} 
//		 /*else if(_instruction instanceof ASTORE_N ) {
//		 	return wp;
//		 }*/ 
//		else if( _instruction instanceof ATHROW ) {
////			//..., objectref ==> objectref
////		 	if (((BCAthrowInstruction)this).getHandler() != null) {
////		 		return ((BCAthrowInstruction)this).getBranchPostconditionCondition();
////		 	} else {
////		 		
////		 		//Formula _ep = _e_Postcondition.substitute(new EXCEPTIONVariable(getExceptions()[0], FreshIntGenerator.getInt()) , exc_obj );
////		 		return _ep;
////		 	}
//		} else if ( _instruction instanceof BIPUSH  ) {
//			//... ==> ..., value
//			//stack.push(((BIPUSH)_instruction).getValue());
//			return wp;
//		} else if(_instruction instanceof  CHECKCAST ) {
//			//TODO
//		 	return wp;
//		}
//		/* else if( ) {
//		 	return wp;
//		 } else if( ) {
//		 	return wp;
//		 } else if( ) {
//		 	return wp;
//		 } else if( ) {
//		 	return wp;
//		 } else if( ) {
//		 	return wp;
//		 } else if( ) {
//		 	return wp;
//		 } else if( ) {
//		 	return wp;
//		 } */
//		 
//		return wp ;
//	}
	
	
	

	/**
	 * sets the postcondition 
	 */
	private void wpTargeters() {
		
		
	}
	
	public void dump(String _s) {
		
		if (true ) {
			System.out.println(_s);
		}
	}

}
