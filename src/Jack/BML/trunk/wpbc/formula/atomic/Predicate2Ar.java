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
	
	public Predicate2Ar(Expression _term1, Expression _term2, byte _predicateSymbol  ) {
		setPredicateSymbol(_predicateSymbol);
	}
}
