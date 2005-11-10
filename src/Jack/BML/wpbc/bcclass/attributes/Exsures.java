/*
 * Created on 6 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcclass.attributes;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate;
import formula.atomic.Predicate0Ar;
import bcexpression.javatype.JavaObjectType;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class Exsures {
	JavaObjectType excType;
	
	private Formula exsuresFormula;
	/*private Formula modifiesPostcondition;*/
	
	public Exsures(Formula f, JavaObjectType _exc) {
		exsuresFormula =	f;
		excType = _exc;
	}
	
	
	/**
	 * 
	 * @return Returns the excType after whic the formula must hold
	 */
	public JavaObjectType getExcType() {
		return excType;
	}
	/**
	 * @return
	 */
	public Formula getPredicate() {
		return exsuresFormula;
	}

	
	
	/**
	 * @param modifiesPostcondition The modifiesPostcondition to set.
	 */
	public void setModifiesPostcondition(Formula modifiesPostcondition) {
		if (modifiesPostcondition == null) {
			return;
		}
		if (modifiesPostcondition == Predicate0Ar.TRUE) {
			return;
		}
		exsuresFormula  = Formula.getFormula( exsuresFormula, modifiesPostcondition, Connector.AND );
	}
	
}
