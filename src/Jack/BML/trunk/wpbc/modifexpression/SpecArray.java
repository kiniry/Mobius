/*
 * Created on Sep 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package modifexpression;

import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract class  SpecArray extends Expression {
	public SpecArray() {
	}
	
	public SpecArray(Expression expr) {
		super(expr);	
	}
	public SpecArray(Expression expr1, Expression expr2) {
		super(expr1, expr2);	
	}
}
