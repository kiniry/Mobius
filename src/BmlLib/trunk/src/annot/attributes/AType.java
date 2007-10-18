package annot.attributes;

import annot.bcclass.BCClass;

/**
 * Contains codes for each printable attribute type
 * and commonly used bit masks to represent sets of attributes
 * that we want retrieve (through getAllAttribute(int mask) methods).
 * TODO w czym te kody sa wykorzystywane? 
 *
 * @see BCClass#getAllAttributes(int)
 * @author tomekb
 */
public interface AType {

	// attribute masks:
	
	/**
	 * Attribute mask that admits all the attribute types
	 */
	public static final int C_ALL = 0xffffffff;

	// attribute codes (must be in (1<<n) form, for n=0,1,2,...)
	
	/**
	 * Single assert code
	 */
	public static final int C_ASSERT = 1;
	
	/**
	 * Method specifications code
	 */
	public static final int C_METHODSPEC = 2;
	
	/**
	 * Class invariant code
	 */
	public static final int C_CLASSINVARIANT = 4;

}
