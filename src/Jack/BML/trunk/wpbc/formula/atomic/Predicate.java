/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package formula.atomic;

import formula.Formula;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class Predicate extends Formula {
	private byte predicateSymbol;
	
	
	public static final TRUE  _TRUE = TRUE.getTRUE();
	public static final FALSE  _FALSE = FALSE.getFALSE();
	
	
	protected void setPredicateSymbol(byte _predicateSymbol) {
		predicateSymbol =  _predicateSymbol;
	}
	public byte getPredicateSymbol() {
		return predicateSymbol;
	}
}
