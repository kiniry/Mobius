/*
 * Created on May 11, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package formula.atomic;

import formula.Formula;
import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class FALSE extends Predicate0Ar {
	private static final FALSE _false = new FALSE();
	private FALSE() {
	}
	
	public static FALSE  getFALSE() {
		return _false;
	}
	
	public Formula substitute(Expression _e, Expression _v) { 
		return this;
	}
	
	public String toString() {
		return "FALSE";
	}

}
