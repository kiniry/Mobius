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
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class ArrayAccessExpression extends Expression {
	
	protected JavaType type;
	
	public ArrayAccessExpression(Expression  _left, Expression _arrIndex  ) {
		setLeft(_left);
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
