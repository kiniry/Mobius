/*
 * Created on Mar 4, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;

import org.apache.bcel.generic.LocalVariableGen;


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
	
	public BCLocalVariable(String _name, int _start_pc,  int _index,  JavaType _type ) {
		name = _name;
		start_pc = _start_pc;
		index = _index;
		type = _type;
	}

	public BCLocalVariable(LocalVariableGen lv) {
		this(lv.getName(), lv.getStart().getPosition() ,  lv.getIndex(), JavaType.getJavaType( lv.getType()));	
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
		if (expr == this) {
			return true;
		}
		return false;
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
		BCLocalVariable copy = new BCLocalVariable(name, start_pc, index, type);
		return copy;
	}
	
	public Expression atState(int instrIndex) { 
		ValueOfConstantAtState valueOfLocalVarAtIndex = new ValueOfConstantAtState( this, instrIndex);
		return valueOfLocalVarAtIndex;
	}

}
