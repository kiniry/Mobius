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
public class TRUE extends Predicate0Ar {
	private static final TRUE _true = new TRUE();
	
	private TRUE() {
	}

	public static TRUE getTRUE() {
			return _true;
	}
	
	public Formula substitute(Expression _e, Expression _v) { 
		return this;
	}
	
	public String toString() {
			return "TRUE";
	}
}
