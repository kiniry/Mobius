package annot.bcexpression.jml;

import annot.bcexpression.Expression;

public  abstract class JMLExpression extends Expression {

	protected JMLExpression() {
	}
	
	public JMLExpression(Expression _e) {	
		super(_e);		
	}
	
	public JMLExpression(Expression _e1, Expression _e2) {	
		super(_e1, _e2);		
	}
}
