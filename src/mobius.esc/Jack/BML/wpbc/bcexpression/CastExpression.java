/*
 * Created on Jul 29, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;

import bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 * 
 * (Type )java_expr
 */
public class CastExpression extends Expression {

	public CastExpression(JavaType type, Expression expr) {
		super(type, expr);
	}

	/**
	 * 
	 * @return the java type that the cast expression must  be cast to, i.e.
	 * (JavaType, Expression ) --> JavaType 
	 */
	public Expression getCastType() {
		Expression type = getSubExpressions()[0];
		return type;
	}

	/**
	 * 
	 * @return the java expression that must  be cast , i.e.
	 * (JavaType, Expression ) --> Expression
	 */
	public Expression getCastExpression() {
		Expression expr = getSubExpressions()[1];
		return expr;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		
		if (equals(_e1)) {
			return _e2;
		}
		Expression[] e = getSubExpressions();
		e[1] = e[1].substitute(_e1, _e2);
		return this;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		return getCastType();
		
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = "( " + getSubExpressions()[0]+ " ) " + getSubExpressions()[1]; 
		return s;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		JavaType type = (JavaType)getSubExpressions()[0];
		Expression e = getSubExpressions()[1].copy();
		CastExpression copy = new CastExpression( type, e);
		return copy;
	}

}
