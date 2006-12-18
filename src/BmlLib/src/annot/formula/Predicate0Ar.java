package annot.formula;

import annot.bcexpression.Expression;

public class Predicate0Ar extends Predicate {

	public static final Predicate0Ar  FALSE = new Predicate0Ar();
	public static final Predicate0Ar  TRUE = new Predicate0Ar();

	private Predicate0Ar() {	
	}
	
//	public Expression copy() {
//		return this;
//	}
//
//	public Expression substitute(Expression _e, Expression _v) {
//		return this;
//	}
	
	public String toString() {
		if (this.equals( Predicate0Ar.TRUE)) {
			return "TRUE";
		} else if(this.equals( Predicate0Ar.FALSE) ) {
			return "FALSE";
		}
		return null;
	}
	
//	public boolean equals(Formula formula) { 
//		
//		if( this  == formula) {
//			return true;
//		}
//		return false;
//	}
//	
//	public Expression simplify() {
//		return this;
//	}
}
