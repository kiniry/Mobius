package bcclass.attributes;
import java.util.HashMap;

import formula.Formula;
import formula.atomic.Predicate;
/**
 * @author Mariela
 * 
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates. To enable and disable the creation of
 * type comments go to Window>Preferences>Java>Code Generation.
 */
public class ExsuresTable implements BCAttribute {
	private HashMap excPostcondition;
	/**
	 * @param exsures -a
	 *            n array of exsuers objects with which the internal hashmap is
	 *            initialised
	 */
	public ExsuresTable(Exsures[] exsures) {
		excPostcondition = new HashMap();
		for (int i = 0; i < exsures.length; i++) {
			excPostcondition.put(exsures[i].getExcType().getSignature(),
					exsures[i]);
		}
	}
	
	public Formula getExcPostconditionFor(String exc_class_name) {
		Exsures exs;
		//if for this exception thrown no postcondition is specified, the default one is returned - TRUE
		if( ( exs = (Exsures)excPostcondition.get(exc_class_name)) == null) {
			return Predicate._TRUE;
		}
		return exs.getPredicate();
		
	}
}
