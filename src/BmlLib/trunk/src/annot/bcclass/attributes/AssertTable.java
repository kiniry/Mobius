/*
 * Created on 6 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package annot.bcclass.attributes;

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

	public Assert getAtPC(int pc, int n) {
		for (int i=asserts.length-1; i>=0; i--)
			if (asserts[i].pcIndex == pc) {
				if (--n == 0)
					return asserts[i];
			}
		System.err.println("(AssertTable) Attribute not found!");
		return null;
	}

}
