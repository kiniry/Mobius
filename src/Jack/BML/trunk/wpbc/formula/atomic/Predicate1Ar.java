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
public class Predicate1Ar extends Predicate {
	private Expression term;
	private byte predicateSymbol;
	
	public Predicate1Ar(Expression _term, byte _predicateSymbol) {
		setPredicateSymbol(_predicateSymbol);
		term = _term;
	} 
	
	public Expression getTerm() {
		return  term;
	}
	
	public Formula substitute(Expression _e,  Expression _v) {
		term.substitute(_e, _v);
		return this;
	}
	
	
	public Formula copy() {
		 Expression termCopy =	term.copy();
		 Predicate1Ar copy = new Predicate1Ar(termCopy, predicateSymbol);
		 return copy;
	}

}
