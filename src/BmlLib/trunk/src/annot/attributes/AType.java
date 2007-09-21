package annot.attributes;

/**
 * Contains codes for each printable attribute type
 * and common used bit mask represents sets of attributes
 * that we want get (in getAllAttribute(int mask) methods).
 * 
 * @author tomekb
 */
public interface AType {

	// attribute masks:
	
	/**
	 * Attribute mask for all attribute types
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
