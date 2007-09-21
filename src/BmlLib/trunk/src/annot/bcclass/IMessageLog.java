package annot.bcclass;

/**
 * This interface contains message priorities and bitmask
 * to control witch type of messages should be displayed.
 * 
 * @see MLog
 * @author tomekb
 */
public interface IMessageLog {
	
	// message type bit masks:
	
	/**
	 * Displays all messages.
	 */
	public static final int PDEBUG = 63;

	/**
	 * Displays all except debug messages.
	 */
	public static final int PNORMAL = 62;

	/**
	 * Displays only error messages.
	 */
	public static final int PERRORS = 32;

	/**
	 * Displays no messages.
	 */
	public static final int PNONE = 0;

	// message types (priorities) - higher message type value,
	// higher it's priority:

	/**
	 * For debug message that appear frequently,
	 * trashing the console.
	 */
	public static final int PDebug = 1;

	/**
	 * For debug message that occures about once per
	 * attribute operation (adding / modifying / removing
	 *  / saving / loading / etc).
	 */
	public static final int PInfo = 2;

	/**
	 * For debug message that appears rarely, about once per
	 * class operation (saving / loading / etc).
	 */
	public static final int PNotice = 4;

	/**
	 * For displaing progress while saving / loading
	 */
	public static final int PProgress = 8;

	/**
	 * Indicates that it's time to implement missing
	 * code branch to make this test case run correctly.
	 */
	public static final int PTodo = 16;

	/**
	 * For displaying error messages.
	 */
	public static final int PError = 32;

}
