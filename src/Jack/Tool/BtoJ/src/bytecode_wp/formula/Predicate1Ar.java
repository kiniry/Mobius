/*
 * Created on Mar 1, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.formula;

import bytecode_wp.bcexpression.Expression;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Predicate1Ar extends Predicate {
	
	
	public Predicate1Ar(Expression _term, byte _predicateSymbol) {
		super( _term, _predicateSymbol);

	}

	public Expression getTerm() {
		return getSubExpressions()[0];
	}

	public Expression substitute(Expression _e, Expression _v) {
		Expression term = getTerm().substitute(_e, _v);
		setSubExpressions(new Expression[]{term});
		return this;
	}
	/**
	 * renames the terms which this predicate is verified for
	 */
	public Expression rename(Expression _e, Expression _v) {
		Expression term = getTerm().rename(_e, _v);
		setSubExpressions(new Expression[]{term});
		return this;
	}

	public Expression copy() {
		Expression termCopy = getTerm().copy();
		Predicate1Ar copy = new Predicate1Ar(termCopy, getPredicateSymbol());
		return copy;
	}

	/**
	 * substitues  all localvariable l by old(l)
	 * overriden method from super class  @see bcexpression.Expression
	 * @return
	 *//*
	public Expression localVarAtPreState() { 
		Expression term = getTerm().localVarAtPreState();
		setSubExpressions(new Expression[]{term});
		return this;
	}*/
	
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
		boolean termsEq = getTerm().equals(_term);
		return termsEq;
	}
	/*public Expression atState(int instrIndex) {
		Expression term = getTerm().atState(instrIndex);
		setSubExpressions(new Expression[]{term});
		return this;
	}
	
	public Expression removeAtState(int index) {
		Expression term = getTerm().removeAtState(index);
		return this;
	}*/
	
	public String toString() {
		String s = "";
		if (getPredicateSymbol() == PredicateSymbol.ODD) {
			s = "odd( " + getTerm().toString() + "  )";
		} else if (getPredicateSymbol() == PredicateSymbol.EVEN) {
			s = "even( " + getTerm().toString() + "  )";
		}
		return s;
	}

}
