/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import bcexpression.javatype.JavaArrType;
import bcexpression.javatype.JavaType;
import type.BCType;


/**
 * @author mpavlova
 * the class represents array access expression, i.e.  a[i]
 */
public class ArrayAccessExpression extends Expression {
	
	protected JavaType type;
	
	/**
	 * @param _array the array object whose element at index _arrIndex is accessed 
	 * @param _arrIndex
	 */
	public ArrayAccessExpression(Expression  _array, Expression _arrIndex  ) {
		setLeft(_array);
		setRight(_arrIndex);
	}


	public BCType getType( ) {
		return type;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		type = ((JavaArrType)getLeft().getType()).getElementType();		
	}
}
