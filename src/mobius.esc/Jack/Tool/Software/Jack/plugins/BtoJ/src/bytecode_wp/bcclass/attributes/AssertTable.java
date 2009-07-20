/*
 * Created on 6 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.bcclass.attributes;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class AssertTable implements BCAttribute {
	private Assert[] asserts;
	
	public AssertTable(Assert[] _asserts ) {
		asserts = _asserts;
	} 
	
	
	/**
	 * @return
	 */
	public Assert[] getAsserts() {
		return asserts;
	}


}
