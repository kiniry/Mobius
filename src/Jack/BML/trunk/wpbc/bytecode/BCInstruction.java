/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

import java.util.Vector;

import org.apache.bcel.generic.*;



import bcclass.BCLocalVariable;
import bcexpression.ExceptionVariable;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.ExpressionFactory;
import bcexpression.type.JavaArrType;
import bcexpression.type.JavaType;
import bcexpression.type.JavaTypeFactory;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

import utils.FreshIntGenerator;
import utils.Util;
import vm.Stack;



/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCInstruction  implements ByteCode{

	protected Formula wp;
	
	private InstructionHandle instructionHandle;	
	private BCInstruction prev;
	private BCInstruction next;
	private Vector targeters;

	private int index;
	private int offset;
	
	/**
	 * exceptions that this throw instruction may cause
	 */
	private JavaType[] exceptions;
	
	public BCInstruction(InstructionHandle  _instruction)  {
		instructionHandle = _instruction; 
		setExceptions(_instruction);

	}

	public JavaType[] getExceptions() {
		return exceptions;
	}
	
	private void setExceptions(InstructionHandle  _instruction) {
		if (exceptions != null ){
			return;
		}
		if ( !(_instruction.getInstruction() instanceof ExceptionThrower)) {
			return;
		}
		Class[] _exceptions = ((ExceptionThrower)_instruction.getInstruction()).getExceptions();
		if (_exceptions == null || _exceptions.length == 0 ){
			return;
		}
		exceptions = new JavaType[_exceptions.length];
		for (int i = 0; i < _exceptions.length; i++) {
			exceptions[i] = JavaTypeFactory.getJavaTypeFactory().getJavaType(_exceptions[i]);
		//	Util.dump(exceptions[i].toString());
		}
	}
	
	public InstructionHandle getInstructionHandle() {
		return instructionHandle;
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
	 * this command appears in the bytecode sequence
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
		return instructionHandle.getPosition();
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
	public Formula wp(Formula _n_Postcondition, Formula _e_Postcondition, Stack stack, ConstantPoolGen _cp) {
		if (wp != null) {
			return wp;
		}
		Instruction _instruction = instructionHandle.getInstruction();
		Vector _subexpr ;
		
		if ((_instruction instanceof  ArrayInstruction) && (_instruction instanceof StackProducer)) {
//			AALOAD, BALOAD, LALOAD, CALOAD, IALOAD, DALOAD , FALOAD, SALOAD
			_subexpr = new Vector();
			int index = ((Integer)stack.pop()).intValue();
			Expression _left = (Expression)stack.pop();
			_subexpr.add(_left);
			_subexpr.add(new Integer(index));
			Expression _expr= ExpressionFactory.getExpressionFactory().getExpression(_subexpr, ExpressionConstants.ARRAYACCESS);
			stack.push(_expr);
			wp = _n_Postcondition;
			return wp;
		} else if( (_instruction instanceof  ArrayInstruction) && (_instruction instanceof StackConsumer)) {
			//TYPE_STORE		
			_subexpr = new Vector();
			Object value = (Object)stack.pop();
			int index = ((Integer)stack.pop()).intValue();
			Expression _left = (Expression)stack.pop();
			_subexpr.add(_left);
			_subexpr.add(new Integer(index));
			Expression _expr= ExpressionFactory.getExpressionFactory().getExpression(_subexpr, ExpressionConstants.ARRAYACCESS);
			wp = _n_Postcondition.substitute(_expr, value);
			return wp;
		} else if ( _instruction instanceof ACONST_NULL) {
			Expression _expr= ExpressionFactory.getExpressionFactory().getExpression(null, ExpressionConstants.NULL);
			stack.push(_expr);
			wp = _n_Postcondition;
			return wp;
		} else if (_instruction instanceof LoadInstruction ) {
			_subexpr = new Vector();
			int _index = ((LoadInstruction)_instruction).getIndex();
			Type _type = ((LoadInstruction)_instruction).getType(_cp);
			_subexpr.add(new BCLocalVariable(_index, _type));
			
			Expression  _expr = ExpressionFactory.getExpressionFactory().getExpression( _subexpr, ExpressionConstants.OBJECTACCESS);
			stack.push(_expr); 
			return wp;
		}
		/*else if (_instruction instanceof  ALOAD_N) {
			
		}*/
		else if (_instruction instanceof ANEWARRAY ) {
			//..., count ==> ..., arrayref
		 	_subexpr = new Vector();
		 	int length = ((Integer)stack.pop()).intValue();
		 	_subexpr.add(new Integer(length));
		 	Expression intLiteral = ExpressionFactory.getExpressionFactory().getExpression( _subexpr, ExpressionConstants.INT_LITERAL);
		 	_subexpr.removeAllElements();
		 	_subexpr.add(new Integer(0));
		 	Expression _0 = ExpressionFactory.getExpressionFactory().getExpression( _subexpr, ExpressionConstants.INT_LITERAL);
		 	
		 	int fresh = FreshIntGenerator.getInt();
		 	_subexpr.add(new Integer(fresh));
		 	_subexpr.add(new ArrayType(((ANEWARRAY)_instruction ).getType(_cp), length )) ;
		 	Expression _expr = ExpressionFactory.getExpressionFactory().getExpression( _subexpr, ExpressionConstants.REFERENCE);
		 	stack.push(_expr);
		 	
		 	Formula _wp1 = new Formula( new Predicate2Ar(intLiteral, _0, PredicateSymbol.GRTEQ), _n_Postcondition  , Connector.IMPLIES ) ;
		 	Formula _wp2 = new Formula( new Predicate2Ar(intLiteral, _0, PredicateSymbol.LESS), _e_Postcondition  , Connector.IMPLIES ) ;
		 	wp = new Formula(_wp1, _wp2, Connector.AND );
		 	return wp;
		} else if(_instruction instanceof ARETURN ) {
		  	Object _ret = stack.pop();
		  	Expression _expr = ExpressionFactory.getExpressionFactory().getExpression( null, ExpressionConstants.RESULT);
		  	wp.substitute(_expr, _ret );
		  	return wp;
		} else if(_instruction instanceof  ARRAYLENGTH ) {
		 	//..., arrayref ==> ..., length
		   int length = ((JavaArrType)((Expression)stack.pop()).getType()).getSize();
		   stack.push( new Integer(length));
		} else if(_instruction instanceof ASTORE ) {
		  	//..., objectref  ==> ...
			_subexpr = new Vector();
			Object _obj = stack.pop();
		 	int _lvIndex = ((ASTORE )_instruction).getIndex();
		 	Type _type = ((ASTORE )_instruction).getType(_cp);
		 	BCLocalVariable _lv = new BCLocalVariable(_lvIndex, _type);
		 	_subexpr.add(_lv);
		 	Expression _expr = ExpressionFactory.getExpressionFactory().getExpression( _subexpr, ExpressionConstants.OBJECTACCESS); 
			wp.substitute(_expr, _obj);
		 	return wp;
		} 
		 /*else if(_instruction instanceof ASTORE_N ) {
		 	return wp;
		 }*/ 
		else if( _instruction instanceof ATHROW ) {
			//..., objectref ==> objectref
		 	if (((BCAthrowInstruction)this).getHandler() != null) {
		 		return ((BCAthrowInstruction)this).getBranchPostconditionCondition();
		 	} else {
		 		Object exc_obj = stack.pop();
		 		Formula _ep = _e_Postcondition.substitute(new ExceptionVariable(getExceptions()[0], FreshIntGenerator.getInt()) , exc_obj );
		 		return _ep;
		 	}
		} else if ( _instruction instanceof BIPUSH  ) {
			//... ==> ..., value
			stack.push(((BIPUSH)_instruction).getValue());
			return wp;
		} else if(_instruction instanceof  CHECKCAST ) {
			//TODO
		 	return wp;
		}
		/* else if( ) {
		 	return wp;
		 } else if( ) {
		 	return wp;
		 } else if( ) {
		 	return wp;
		 } else if( ) {
		 	return wp;
		 } else if( ) {
		 	return wp;
		 } else if( ) {
		 	return wp;
		 } else if( ) {
		 	return wp;
		 } */
		 
		return wp ;
	}

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
