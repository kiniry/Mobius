package bcclass.attributes;
import java.util.Collection;
import java.util.HashMap;

import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate;
import formula.atomic.Predicate0Ar;
/**
 * @author Mariela
 * 
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates. To enable and disable the creation of
 * type comments go to Window>Preferences>Java>Code Generation.
 */
public class ExsuresTable implements BCAttribute {
	private Exsures[] excPostcondition;
	
/*	protected void setModifiedPostCondition(Formula _modifiesPostcondition) {
		for (int i = 0; i < excPostcondition.length; i++) {
			excPostcondition[i].setModifiesPostcondition((Formula)_modifiesPostcondition.copy());
		}
	}*/
	

	/**
	 * @param exsures -a
	 *            n array of exsuers objects with which the internal hashmap is
	 *            initialised
	 */
	public ExsuresTable(Exsures[] exsures) {
		excPostcondition = exsures;
	}
	
	
	public Formula getExcPostconditionFor(String exc_class_name) {
		Exsures exs;

		JavaObjectType exception = (JavaObjectType)JavaType.getJavaRefType(exc_class_name);
		Exsures exsures = null;
		for (int i = 0; i < excPostcondition.length; i++)  {
			JavaObjectType _type = excPostcondition[i].getExcType();
			if ( (exsures == null) && (JavaObjectType.subType(exception, _type ))) {
				exsures = excPostcondition[i];
				continue;
			}
			// if the next exsures has  more specific type then is should be the one to  determine the exc postcondition
			if (JavaObjectType.subType( exception , excPostcondition[i].getExcType() )  && JavaObjectType.subType( excPostcondition[i].getExcType(), exsures.getExcType() )) {
				exsures = excPostcondition[i];
			}
		}
		// if no exc postcondition specificied for  this exception, then return false by default
		if (exsures == null) {
			return Predicate0Ar.FALSE;
		}
		Formula exsFormula = (Formula)exsures.getPredicate().copy();
		return exsFormula;
	}

	/**
	 * @return Returns the excPostcondition.
	 */
	public Exsures[] getExsures() {
		
		return excPostcondition;
	}
	
}
