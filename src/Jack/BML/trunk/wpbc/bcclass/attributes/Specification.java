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
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class Specification  {
	private Formula predicate;
	
	public Specification( Formula _f) {
		predicate = _f;
	}
	
	
	public Formula getPredicate() {
		return predicate;
	}
}
