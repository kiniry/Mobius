/*
 * Created on May 11, 2004
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
public class Predicate0Ar extends Predicate {

	public Expression copy() {
		return this;
	}

	public Expression substitute(Expression _e, Expression _v) {
		return this;
	}
	
	public String toString() {
		if (this.equals( Predicate.TRUE)) {
			return "TRUE";
		} else if(this.equals( Predicate.FALSE) ) {
			return "FALSE";
		}
		return null;
	}
	
	public boolean equals(Formula formula) { 
		
		if( this  == formula) {
			return true;
		}
		return false;
	}
}
