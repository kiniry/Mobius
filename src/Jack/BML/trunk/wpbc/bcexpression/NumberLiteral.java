/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import bcexpression.javatype.JavaBasicType;
import bcexpression.javatype.JavaType;
import type.BCType;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class NumberLiteral extends Expression {
//	private Number literal;
	private int radix;
	private String literal;
	private JavaBasicType type;
	
	/**
	 * this constructor expects that _literal must be a correct representation of an integer litreral.
	 * @param _literal - a string representation of integer
	 * e.g. new  NumberLiteral("12")
	 */
	public NumberLiteral(String _literal) {
		this(_literal, 10, JavaType.JavaINT);
	}

	/**
	 * this constructor expects that _literal must be a correct representation of an integer litreral.
	 * @param _literal - a string representation of integer
	 * e.g. new  NumberLiteral("12")
	 */
	public NumberLiteral(int _literal) {
		this(Integer.toString(_literal), 10,JavaType.JavaINT);
	}
	
	/**
	 * 
	 * @param value - a correct value
	 * @param radix - the radix in which the value is interpreted
	 */
	public NumberLiteral(String _literal, int _radix, JavaBasicType _type) {
		literal = _literal;
		radix = _radix;
		type = _type;
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
		return type;
	}
}
