/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.bcexpression.jml;

import bytecode_wp.bcexpression.Expression;




/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public  abstract class JMLExpression extends Expression {
	//private JavaType type;
	
	

	protected JMLExpression() {
	}
	
	public JMLExpression(Expression _e) {	
		super(_e);		
	}
	
	public JMLExpression(Expression _e1, Expression _e2) {	
		super(_e1, _e2);		
	}

/*	public Expression getTypeOf( Expression expr) {
		if (expr == NULL._NULL) {
			return NULL._NULL.getType();
		}
		if (expr instanceof Reference ) {
			return expr.getType();
		}
		Expression typeOfExpr = new TYPEOF(expr);
		return typeOfExpr;
	}*/
}
