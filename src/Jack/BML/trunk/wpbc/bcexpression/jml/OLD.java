/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.jml;

import type.BCType;
import bcexpression.Expression;
import bcexpression.javatype.JavaType;


/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class OLD extends JMLExpression  {
	
	private JavaType type ;
	
	public OLD(Expression _left) {
		setLeft(_left);
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		type = (JavaType) ((Expression)getLeft()).getType();
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		if (type == null) {
			setType();
		}
		return type;
	}
}
