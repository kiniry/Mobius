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
	
	public Predicate1Ar(Expression _term, byte _predicateSymbol) {
		setPredicateSymbol(_predicateSymbol);
		term = _term;
	}

	public Expression getTerm() {
		return term;
	}

	public Expression substitute(Expression _e, Expression _v) {
		term = term.substitute(_e, _v);
		return this;
	}
	/**
	 * renames the terms which this predicate is verified for
	 */
	public Expression rename(Expression _e, Expression _v) {
		term = term.rename(_e, _v);
		return this;
	}

	public Expression copy() {
		Expression termCopy = term.copy();
		Predicate1Ar copy = new Predicate1Ar(termCopy, getPredicateSymbol());
		return copy;
	}

	public boolean equals(Formula formula) {
		boolean eq = super.equals(formula);
		// if the super class equals returns false then return false
		if (!eq) {
			return false;
		}
		if (getPredicateSymbol()
			!= ((Predicate1Ar) formula).getPredicateSymbol()) {
			return false;
		}
		// else if the super class equals returns  true check if the terms in both predicates are equal 
		Expression _term = ((Predicate1Ar) formula).getTerm();
		boolean termsEq = term.equals(_term);
		return termsEq;
	}
	public Expression atState(int instrIndex) {
		term = term.atState(instrIndex);
		return this;
	}
	
	public Expression removeAtState(int index) {
		term = term.removeAtState(index);
		return this;
	}
	
	public String toString() {
		String s = "";
		if (getPredicateSymbol() == PredicateSymbol.ODD) {
			s = "odd( " + term.toString() + "  )";
		} else if (getPredicateSymbol() == PredicateSymbol.EVEN) {
			s = "even( " + term.toString() + "  )";
		}
		return s;
	}

}
