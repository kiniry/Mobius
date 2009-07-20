/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.formula;

import bytecode_wp.bcexpression.Expression;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class Predicate extends Formula {
	private byte predicateSymbol;
	
	public Predicate(){
		
	}
	public Predicate(
			Expression _term,
			byte _predicateSymbol
			){
		super(_term);
		predicateSymbol = _predicateSymbol;
	}
	public Predicate(
			Expression _term1,
			Expression _term2,
			byte _predicateSymbol
			){
		super(_term1, _term2);
		predicateSymbol = _predicateSymbol;
	}
	
	protected void setPredicateSymbol(byte _predicateSymbol) {
		predicateSymbol =  _predicateSymbol;
	}
	public byte getPredicateSymbol() {
		return predicateSymbol;
	}
	
}
