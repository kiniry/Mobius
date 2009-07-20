/*
 * Created on Mar 4, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;

import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.generic.LocalVariableGen;


import bcclass.BCMethod;
import bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCLocalVariable extends Expression {
	private  int index;
	private  int length;
	private String name;
	private JavaType type; 
	private  int start_pc;
	private BCMethod method ;
	
	// when this a register that doesnot store any local variable
	private static int UNDEF_LEN = -1;
	public BCLocalVariable(String _name, int _start_pc, int _length,  int _index,  JavaType _type , BCMethod _method) {
		name = _name;
		start_pc = _start_pc;
		length = _length;
		index = _index;
		type = _type;
		method = _method;
	}

	public BCLocalVariable(LocalVariable lv, JavaType _type, BCMethod _method) {
		this(lv.getName(), lv.getStartPC() , lv.getLength() ,  lv.getIndex(), _type , _method);	
	}

	/**
	 * this constructor is for constructing a register object that doesnot represent
	 * any local variable
	 * 
	 * @param index
	 * @param _method
	 */
	public BCLocalVariable(int index ,  BCMethod _method) {
		this(null, 0 ,UNDEF_LEN   , index , null , _method);	
	}
	
	/**
	 * @return
	 */
	public int getIndex() {
		return index;
	}

	/**
	 * @return
	 */
	public int getLength() {
		return length;
	}

	/**
	 * @return
	 */
	public int getStart_pc() {
		return start_pc;
	}

//	/**
//	 * @return
//	 */
//	public int getName_index() {
//		return name_index;
//	}
//
//	/**
//	 * @return
//	 */
//	public int getSignature_index() {
//		return signature_index;
//	}
//
	public boolean equals(Expression expr) {
		boolean isEq = super.equals(expr);
		if (!isEq) {
			return false;
		}
		BCLocalVariable locVar = (BCLocalVariable)expr;
		if (locVar.getIndex() != getIndex() ) { 
			return false;
		}
		if ( locVar.getMethod() != method ) {
			return false;
		}
		
		
		/*if (expr == this) {
			return true;
		}*/
		return true;
	}

	/**
	 * @return
	 */
	public Expression getType() {
		return type;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		if (this.equals( _e1)) {
			return _e2.copy();
		}
		return this;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		return "local(" + getIndex() + ")" ;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		BCLocalVariable copy = new BCLocalVariable(name, start_pc, length, index, type, method);
		return copy;
	}
	
	public Expression atState(int instrIndex) { 
		ValueOfConstantAtState valueOfLocalVarAtIndex = new ValueOfConstantAtState( this, instrIndex);
		return valueOfLocalVarAtIndex;
	}

	/**
	 * @return Returns the name.
	 */
	public String getName() {
		return name;
	}
	/**
	 * @param name The name to set.
	 */
	public void setName(String name) {
		this.name = name;
	}
	/**
	 * @return Returns the method.
	 */
	public BCMethod getMethod() {
		return method;
	}
}
