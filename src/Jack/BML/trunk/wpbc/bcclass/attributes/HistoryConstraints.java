/*
 * Created on Jul 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass.attributes;

import formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class HistoryConstraints implements BCAttribute {
	private Formula predicate;
	
	public HistoryConstraints(Formula _predicate) {
		predicate = _predicate;
	}

	/**
	 * @return
	 */
	public Formula getPredicate() {
		return predicate;
	}

}
