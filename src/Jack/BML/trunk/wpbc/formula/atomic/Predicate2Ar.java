/*
 * Created on Mar 1, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package formula.atomic;

import bcexpression.Expression;
import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Predicate2Ar extends Predicate {
	private Expression term1;
	private Expression term2;
	public Predicate2Ar(Expression _term1, Expression _term2, byte _predicateSymbol  ) {
		term1 = _term1;
		term2 = _term2;
		setPredicateSymbol(_predicateSymbol);
	}
	
	public Formula substitute(Expression _e,  Expression _v) {
		term1.substitute(_e, _v);
		term2.substitute(_e, _v);
		return this;
	}
}
