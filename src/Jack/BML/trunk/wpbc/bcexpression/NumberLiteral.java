/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import bcexpression.javatype.JavaType;
import type.BCType;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class NumberLiteral extends Expression {
	private Number literal;
	
	public NumberLiteral(Number _literal) {
		literal = _literal;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		// TODO Auto-generated method stub
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType()  {
		if (literal instanceof Integer ) {
			return JavaType.JavaINT;
		} else if (literal instanceof Float) {
			return JavaType.JavaFLOAT;
		} else if ( literal instanceof Double) {
			return JavaType.JavaDOUBLE;
		} else if (literal instanceof Byte) {
			return JavaType.JavaBYTE;
		} else if (literal instanceof Long) {
			return JavaType.JavaLONG;
		}
		return null;
	}
}
