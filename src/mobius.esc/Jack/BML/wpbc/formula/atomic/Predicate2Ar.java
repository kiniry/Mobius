/*
 * Created on Mar 1, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package formula.atomic;

import bcexpression.Expression;
import bcexpression.NULL;
import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;
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
			) {
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

		// the two terms are number literals 
		int value1 = ((NumberLiteral) _term1).getLiteral();
		int value2 = ((NumberLiteral) _term2).getLiteral();

		if (_predicateSymbol == PredicateSymbol.GRT) {
			if (value1 > value2) {
				p = Predicate0Ar.TRUE;
			} else {
				p = Predicate0Ar.FALSE;
			}
			//			p = ( value1 > value2)?Predicate._TRUE:Predicate._FALSE; 
			return p;
		} else if (_predicateSymbol == PredicateSymbol.GRTEQ) {
			if (value1 >= value2) {
				p = Predicate0Ar.TRUE;
			} else {
				p = Predicate0Ar.FALSE;
			}
			//		p = ( value1 > value2)?Predicate._TRUE:Predicate._FALSE; 
			return p;
		} else if (_predicateSymbol == PredicateSymbol.LESS) {
			if (value1 < value2) {
				p = Predicate0Ar.TRUE;
			} else {
				p = Predicate0Ar.FALSE;
			}
			//		p = ( value1 > value2)?Predicate._TRUE:Predicate._FALSE; 
			return p;
		} else if (_predicateSymbol == PredicateSymbol.LESSEQ) {
			if (value1 <= value2) {
				p = Predicate0Ar.TRUE;
			} else {
				p = Predicate0Ar.FALSE;
			}
			//		p = ( value1 > value2)?Predicate._TRUE:Predicate._FALSE; 
			return p;
		} 
		/*else if (_predicateSymbol == PredicateSymbol.NOTEQ) {
			if (value1 != value2) {
				p = Predicate0Ar.TRUE;
			} else {
				p = Predicate0Ar.FALSE;
			}
			//		p = ( value1 > value2)?Predicate._TRUE:Predicate._FALSE; 
			return p;
		}*/
		return null;
	}

	public static Predicate simplifyEQUALS(
		Expression _term1,
		Expression _term2) {
		if (_term1.equals(_term2)) {
			return Predicate0Ar.TRUE;
		}
		Predicate2Ar p = new Predicate2Ar(_term1, _term2, PredicateSymbol.EQ);
		return p;
	}

	public Expression substitute(Expression _e, Expression _v) {

		//		Util.dump("substitute [" +_e  +"<- " +  _v + "] in"+  term1.toString());	
		
		term1 = term1.substitute(_e, _v);

		term2 = term2.substitute(_e, _v);
		
		Expression simplify = simplify();
		//		Util.dump("term2 substitute [" +_e  +"<- " +  _v + "] =  "+  term2.toString());
		//		Util.dump("term1 substitute [" +_e  +"<- " +  _v + "]"+  term1.toString());
		//		Util.dump("predicate substitute " +  toString());
		/*return this;*/
		return simplify;
	}

	
	  /**
	    * Returns either this object either an object which is a simplification of this one
	    * and which has an equivalent trutrh value of this object 
	    * Simplifications are done respecting these rules
	    * <UL>
	    *     <li> if the predicate is the subtype predicate 
	    * 		  <UL> 
	    * 			  <li> if <code>term1 == JavaType._NULL</code> and term is a <code>JavaRefernceType</code>
	    * 				   @return 	Predicate0ar.TRUE 
	    * 		 	  <li> else @return <code>this</code>
	    * 		 </UL>
	    *     <li> if the predicate is the equal predicate then:  
	    *          <UL>
	    *                <li> if the predicate is of the form  <code>term1 == term2 </code> and term1.equals(term2)
	    * 		           then @return Predicate0ar.TRUE 
	    *                <li> if the predicate is of the form  <code>Predicate0Ar.TRUE == Predicate0Ar.FALSE </code> or
	    *                     <code>Predicate0Ar.FALSE == Predicate0Ar.TRUE</code> @return  Predicate0Ar.FALSE
	    *         	     <li> else @return <code>this</code>
	    * 			</UL>
	    * 
	    *  </UL>
	    **/ 
	protected Expression simplify() {
		if (getPredicateSymbol() ==  PredicateSymbol.SUBTYPE ) { 
			if ( (term1 == JavaType._NULL) && ( term2  instanceof JavaReferenceType ) ) {
				return Predicate0Ar.TRUE; 
			}
			if ( (term1 instanceof JavaReferenceType ) && (term2 instanceof JavaReferenceType )) {
				Predicate0Ar isSubType = ( JavaReferenceType.subType( (JavaReferenceType )term1 , (JavaReferenceType)term2)) ?  Predicate0Ar.TRUE  :  Predicate0Ar.FALSE  ;
				return isSubType;
			}
		}

		if (getPredicateSymbol() ==  PredicateSymbol.EQ) {
			if (term1.equals(term2 )) {
				return Predicate0Ar.TRUE;
			}

			if ( (term1== Predicate0Ar.TRUE ) && (term1== Predicate0Ar.FALSE )) {
				return Predicate0Ar.FALSE;
			}
			if ( (term2 == Predicate0Ar.TRUE ) && (term1 == Predicate0Ar.FALSE )) {
				return Predicate0Ar.FALSE;
			}
		}
		return this;
	}
	
	public Expression rename(Expression _expr1, Expression _expr2) {
		term1 = term1.rename(_expr1, _expr2);
		term2 = term2.rename(_expr1, _expr2);
		return this;
	}


	public String toString() {
		String op = "";
/*		if (getPredicateSymbol() == PredicateSymbol.NOTEQ) {
			op = " != ";
		}*/
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
		if (getPredicateSymbol() == PredicateSymbol.SUBTYPE ) {
			op = " <: ";
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
	
	public Expression atState(int instrIndex) {
		term1 = term1.atState(instrIndex);
		term2 = term2.atState(instrIndex);
		return this;
	}
	
	public Expression removeAtState(int index) {
		term1 = term1.removeAtState(index);
		term2 = term2.removeAtState(index);
		return this;
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
