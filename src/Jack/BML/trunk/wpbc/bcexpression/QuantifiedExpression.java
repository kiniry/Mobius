/*
 * Created on Sep 16, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;

import java.util.Vector;

import formula.Formula;
import formula.Quantificator;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class QuantifiedExpression extends Expression {
	
	
	
	public QuantifiedExpression(Quantificator _q, Expression expr  ) {
		super(_q, expr);
	}
	
	public Expression substitute(Expression _e, Expression _v) {
		//Util.dump(toString());
		
		Quantificator quantificator = (Quantificator)getSubExpressions()[0];
		Expression boundExpr = quantificator.getBoundVar();
		if (_e.equals(boundExpr)) {
			return this;
		}
		Expression subst = getSubExpressions()[1];
		subst = getSubExpressions()[1].substitute(_e,_v);
		return this;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = getSubExpressions()[0] + ". " + getSubExpressions()[1]; 
		return s;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression[] exp = new Expression[2];
		exp[0] = getSubExpressions()[0].copy();
		exp[1] = getSubExpressions()[1].copy();
		QuantifiedExpression qExp = new QuantifiedExpression((Quantificator)exp[0], exp[1] );
		return qExp;
	}
	
	/**
	 * 
	 * @return an array of copied elements of the array
	 */
	public Quantificator[] getQuantificator()  {
		/*return (Quantificator)getSubExpressions()[0];*/
		if (!(getSubExpressions()[1] instanceof QuantifiedExpression ) ) {
			return  new Quantificator[]{(Quantificator)getSubExpressions()[0]};
		}
		
		Quantificator[] _q = ((QuantifiedExpression)getSubExpressions()[1]).getQuantificator();
		Quantificator[] q = new Quantificator[_q.length + 1];
		
		q[0] = (Quantificator)getSubExpressions()[0];
		System.arraycopy(_q, 0, q , 1, _q.length );
		return q;
	}
	
	
	
	public Expression getQuantifiedExpression()  {
		if ( !(getSubExpressions()[1] instanceof QuantifiedExpression )) {
			return getSubExpressions()[1];
		}
		QuantifiedExpression quantifiedExpr = (QuantifiedExpression ) getSubExpressions()[1];;
		Expression expr = quantifiedExpr.getQuantifiedExpression();
		return expr;
	}
}
