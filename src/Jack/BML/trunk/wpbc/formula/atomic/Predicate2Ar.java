/*
 * Created on Mar 1, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package formula.atomic;

import bcexpression.Expression;
import bcexpression.NumberLiteral;
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

	public static Predicate getPredicate(
		Expression _term1,
		Expression _term2,
		byte _predicateSymbol) {
		Predicate p = null;
		if (_predicateSymbol == PredicateSymbol.EQ) {
			p = simplifyEQUALS(_term1, _term2);
		}

		if ((_predicateSymbol == PredicateSymbol.GRT)
			|| (_predicateSymbol == PredicateSymbol.GRTEQ)
			|| (_predicateSymbol == PredicateSymbol.LESS)
			|| (_predicateSymbol == PredicateSymbol.LESSEQ)
			|| (_predicateSymbol == PredicateSymbol.NOTEQ)
			) {
			p = simplifyNUMBERRELATION(_term1, _term2, _predicateSymbol);
		}
		return null;
	}

	public static Predicate simplifyNUMBERRELATION(
		Expression _term1,
		Expression _term2,
		byte _predicateSymbol) {
		Predicate p = null;
		if (!(_term1 instanceof NumberLiteral)
			|| !(_term2 instanceof NumberLiteral)) {
			p = new Predicate2Ar(_term1, _term2, _predicateSymbol);
			return p;
		}

		int value1 = ((NumberLiteral) _term1).getLiteral();
		int value2 = ((NumberLiteral) _term2).getLiteral();

		if (_predicateSymbol == PredicateSymbol.GRT) {
			if (value1 > value2) {
				p = Predicate._TRUE;
			} else {
				p = Predicate._FALSE;
			}
			//			p = ( value1 > value2)?Predicate._TRUE:Predicate._FALSE; 
			return p;
		} else if (_predicateSymbol == PredicateSymbol.GRTEQ) {
			if (value1 >= value2) {
				p = Predicate._TRUE;
			} else {
				p = Predicate._FALSE;
			}
			//		p = ( value1 > value2)?Predicate._TRUE:Predicate._FALSE; 
			return p;
		} else if (_predicateSymbol == PredicateSymbol.LESS) {
			if (value1 < value2) {
				p = Predicate._TRUE;
			} else {
				p = Predicate._FALSE;
			}
			//		p = ( value1 > value2)?Predicate._TRUE:Predicate._FALSE; 
			return p;
		} else if (_predicateSymbol == PredicateSymbol.LESSEQ) {
			if (value1 <= value2) {
				p = Predicate._TRUE;
			} else {
				p = Predicate._FALSE;
			}
			//		p = ( value1 > value2)?Predicate._TRUE:Predicate._FALSE; 
			return p;
		} else if (_predicateSymbol == PredicateSymbol.NOTEQ) {
			if (value1 != value2) {
				p = Predicate._TRUE;
			} else {
				p = Predicate._FALSE;
			}
			//		p = ( value1 > value2)?Predicate._TRUE:Predicate._FALSE; 
			return p;
		}
		return null;
	}

	public static Predicate simplifyEQUALS(
		Expression _term1,
		Expression _term2) {
		if (_term1.equals(_term2)) {
			return Predicate._TRUE;
		}
		Predicate2Ar p = new Predicate2Ar(_term1, _term2, PredicateSymbol.EQ);
		return p;
	}

	public Predicate2Ar(
		Expression _term1,
		Expression _term2,
		byte _predicateSymbol) {
		term1 = _term1;
		term2 = _term2;
		setPredicateSymbol(_predicateSymbol);
	}

	public Formula substitute(Expression _e, Expression _v) {
		term1 = term1.substitute(_e.copy(), _v.copy());
		term2 = term2.substitute(_e.copy(), _v.copy());
		return this;
	}

	public String toString() {
		String op = "";
		if (getPredicateSymbol() == PredicateSymbol.NOTEQ) {
			op = " != ";
		}
		if (getPredicateSymbol() == PredicateSymbol.EQ) {
			op = " == ";
		}
		if (getPredicateSymbol() == PredicateSymbol.GRT) {
			op = " > ";
		}
		if (getPredicateSymbol() == PredicateSymbol.GRTEQ) {
			op = " >= ";
		}
		if (getPredicateSymbol() == PredicateSymbol.LESS) {
			op = " < ";
		}
		if (getPredicateSymbol() == PredicateSymbol.LESSEQ) {
			op = " <= ";
		}

		return "(" + term1 + op + term2 + ")";

	}
	
	
	public Formula copy() {
		Expression term1Copy = term1.copy();
		Expression term2Copy = term2.copy();
		Predicate2Ar copy = new Predicate2Ar(term1Copy, term2Copy, getPredicateSymbol());
		return copy;
	}	

}
