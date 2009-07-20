/*
 * Created on Apr 14, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package bytecode_wp.bcclass.attributes;

/**
 * @author mpavlova
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class SETTable  implements BCAttribute {
	private SET[] set;
	
	public SETTable(SET[] _asserts ) {
		set = _asserts;
	} 
	
	
	/**
	 * @return
	 */
	public SET[] getAsserts() {
		return set;
	}


}
