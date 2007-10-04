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
	public static final int PALL = 127;

	/**
	 * Displays almost all messages.
	 */
	public static final int PDEBUG = 126;

	/**
	 * Displays all except debug messages.
	 */
	public static final int PNORMAL = 124;

	/**
	 * Displays only error messages.
	 */
	public static final int PERRORS = 64;

	/**
	 * Displays no messages.
	 */
	public static final int PNONE = 0;

	// message types (priorities) - higher message type value,
	// higher it's priority:

	/**
	 * For debug message that appear very frequently
	 * (or that are very long), slowing down the library.
	 */
	public static final int PDebug2 = 1;

	/**
	 * For debug message that appear frequently,
	 * trashing the console.
	 */
	public static final int PDebug = 2;

	/**
	 * For debug message that occures about once per
	 * attribute operation (adding / modifying / removing
	 *  / saving / loading / etc).
	 */
	public static final int PInfo = 4;

	/**
	 * For debug message that appears rarely, about once per
	 * class operation (saving / loading / etc).
	 */
	public static final int PNotice = 8;

	/**
	 * For displaing progress while saving / loading
	 */
	public static final int PProgress = 16;

	/**
	 * Indicates that it's time to implement missing
	 * code branch to make this test case run correctly.
	 */
	public static final int PTodo = 32;

	/**
	 * For displaying error messages.
	 */
	public static final int PError = 64;

}
