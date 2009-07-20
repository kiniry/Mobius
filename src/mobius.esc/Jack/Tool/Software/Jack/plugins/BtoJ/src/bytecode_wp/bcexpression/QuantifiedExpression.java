/*
 * Created on Sep 16, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcexpression;



import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Quantificator;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class QuantifiedExpression extends Expression {
	
	
	//private Expression domain;
	public QuantifiedExpression(Quantificator _q, Formula domain , Expression expr  ) {
		super(new Expression[]{_q,domain, expr});
		/*this.domain = domain;*/
	}
	
	public Expression substitute(Expression _e, Expression _v) {
		//Util.dump(toString());	
		Quantificator quantificator = (Quantificator)getSubExpressions()[0];
		Expression[] boundExpr = quantificator.getBoundVars();
		for (int s = 0; s < boundExpr.length; s++) {
			if (_e.equals(boundExpr[s])) {
				return this;
			}
		}
	    getSubExpressions()[1].substitute(_e,_v);
		getSubExpressions()[2].substitute(_e,_v);
		return this;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = "" + getSubExpressions()[0]  + getSubExpressions()[1] + "."+ getSubExpressions()[2] ; 
		return s;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression[] exp = new Expression[2];
		exp[0] = getSubExpressions()[0].copy();
		exp[1] = getSubExpressions()[2].copy();
		Formula domainC = (Formula)getSubExpressions()[1].copy();
		QuantifiedExpression qExp = new QuantifiedExpression((Quantificator)exp[0], domainC,  exp[1] );
		return qExp;
	}
	
	/**
	 * 
	 * @return an array of copied elements of the array
	 */
	public Quantificator getQuantificator()  {
		Quantificator q = (Quantificator)getSubExpressions()[0].copy();
		return q;
	}
	
	public Formula getDomain()  {
		Formula f = (Formula)getSubExpressions()[1].copy();
		return f;
	}
	
	public Expression getTheExpressionQuantified()  {
		//if ( !(getSubExpressions()[2] instanceof QuantifiedExpression )) {
			return getSubExpressions()[2];
		//}
		//QuantifiedExpression quantifiedExpr = (QuantifiedExpression ) getSubExpressions()[2];
		//Expression expr = quantifiedExpr.getTheExpressionQuantified();
		//return expr;
	}
}
