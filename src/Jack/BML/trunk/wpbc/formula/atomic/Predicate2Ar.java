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

	public Predicate2Ar(
		Expression _term1,
		Expression _term2,
		byte _predicateSymbol) {
		term1 = _term1;
		term2 = _term2;
		setPredicateSymbol(_predicateSymbol);
	}

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
			|| (_predicateSymbol == PredicateSymbol.NOTEQ)) {
			p = simplifyNUMBERRELATION(_term1, _term2, _predicateSymbol);
		}
		return p;
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
				p = Predicate.TRUE;
			} else {
				p = Predicate.FALSE;
			}
			//			p = ( value1 > value2)?Predicate._TRUE:Predicate._FALSE; 
			return p;
		} else if (_predicateSymbol == PredicateSymbol.GRTEQ) {
			if (value1 >= value2) {
				p = Predicate.TRUE;
			} else {
				p = Predicate.FALSE;
			}
			//		p = ( value1 > value2)?Predicate._TRUE:Predicate._FALSE; 
			return p;
		} else if (_predicateSymbol == PredicateSymbol.LESS) {
			if (value1 < value2) {
				p = Predicate.TRUE;
			} else {
				p = Predicate.FALSE;
			}
			//		p = ( value1 > value2)?Predicate._TRUE:Predicate._FALSE; 
			return p;
		} else if (_predicateSymbol == PredicateSymbol.LESSEQ) {
			if (value1 <= value2) {
				p = Predicate.TRUE;
			} else {
				p = Predicate.FALSE;
			}
			//		p = ( value1 > value2)?Predicate._TRUE:Predicate._FALSE; 
			return p;
		} else if (_predicateSymbol == PredicateSymbol.NOTEQ) {
			if (value1 != value2) {
				p = Predicate.TRUE;
			} else {
				p = Predicate.FALSE;
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
			return Predicate.TRUE;
		}
		Predicate2Ar p = new Predicate2Ar(_term1, _term2, PredicateSymbol.EQ);
		return p;
	}

	public Expression substitute(Expression _e, Expression _v) {

		//		Util.dump("substitute [" +_e  +"<- " +  _v + "] in"+  term1.toString());	
		term1 = term1.substitute(_e, _v);

		term2 = term2.substitute(_e, _v);
		//		Util.dump("term2 substitute [" +_e  +"<- " +  _v + "] =  "+  term2.toString());
		//		Util.dump("term1 substitute [" +_e  +"<- " +  _v + "]"+  term1.toString());
		//		Util.dump("predicate substitute " +  toString());
		return this;
	}

	
	public Expression rename(Expression _expr1, Expression _expr2) {
		term1 = term1.rename(_expr1, _expr2);
		term2 = term2.rename(_expr1, _expr2);
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

	public Expression copy() {
		Expression term1Copy = term1.copy();
		Expression term2Copy = term2.copy();
		Predicate2Ar copy =
			new Predicate2Ar(term1Copy, term2Copy, getPredicateSymbol());
		return copy;
	}

	public Expression getLeftExpression() {
		return term1;
	}
	
	public Expression getRightExpression() {
		return term2;
	}
	public boolean equals(Formula formula) { 
		boolean eq = super.equals(formula);
		// if the super class equals returns false then return false
		if (!eq ) {
			return false;
		}
		if (getPredicateSymbol() != ((Predicate2Ar)formula).getPredicateSymbol()) {
			return false;
		}
		Expression _term1 = ((Predicate2Ar)formula).getLeftExpression();
		Expression _term2 = ((Predicate2Ar)formula).getRightExpression();
		
		boolean termsEq = term1.equals( _term1) &&  term2.equals(_term2);
		return termsEq;
	}
}
