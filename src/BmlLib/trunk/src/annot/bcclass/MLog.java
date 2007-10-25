package annot.bcclass;

/**
 * A standard logging utility. Use this instead of writing
 * anything to stdout (except tests classes). All messages
 * with priority : priority & mask > 0 will be displayed to
 * stdout, all others will be ingnored.
 * 
 * @author tomekb
 */
public class MLog implements IMessageLog {

	/**
	 * Message type filter. It's not final, so it can be
	 * changed eg. by automated tests.
	 */
	public static int mask = PNORMAL;

	/**
	 * Displays a message to the standard output
	 * iff it is important enough.
	 * 
	 * @param priority - message priority,
	 * @param msg - message text.
	 */
	public static void putMsg(int priority, String msg) {
		if ((priority & mask) > 0)
			System.out.println(msg);
	}

}
