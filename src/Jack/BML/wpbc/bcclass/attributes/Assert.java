/*
 * Created on 6 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcclass.attributes;

import formula.Formula;

/**
 * @author io
 * 
 *   
 */
public class Assert {
	

	// the position in the bytecode where the predicate must hold
	private int position;
	
	private Formula assertFormula;
	public Assert(Formula _f, int _p) {
			assertFormula = _f;
			position = _p;
	}	
	
	/**
	 * 
	 * @return Returns the position where the predicate must hold
	 */
	public int getPosition() {
		return position;
	}
	
	/**
	 * @return
	 */
	public Formula getPredicate() {
		return assertFormula;
	}
}
