package navmid.graph;

/**
 * A CallbackNode represents a callback method in a listener class (abstracted by a {@link ListenerClassNode}.
 * It treats a given kind of events.
 * 
 * @author piac6784
 *
 */
public class CallbackNode extends Node {
	/**
	 * Enumeration listing all the kinds of events that can  be treated by callbacks.
	 * @author piac6784
	 *
	 */
	public enum Event {
		/**
		 * Commands are soft buttons associated to screen 
		 */
		COMMAND, 
		/**
		 * Items are elements of forms. They have their own commands.
		 */
		ITEM, 
		/**
		 * Change in the state of an item (usually the value represented by this item).
		 */
		ITEM_STATE, 
		/**
		 * Canvas have different kinds or raw pointers and keyboard events.
		 */
		CANVAS, 
		/**
		 * The start of the midlet by the AMS with a call to <code>MIDlet.start</code>.
		 */
		START, 
		/**
		 * Initialization of the midlet (the constructor). There should be no GUI actions in it. 
		 */
		INIT, 
		/**
		 * Stopping the midlet. 
		 */
		STOP, 
		/**
		 * A thread launch (not handled yet).
		 */
		THREAD, 
		/**
		 * Other not handled events.
		 */
		UNDEFINED };
		
	public final Event purpose; 
	
	public final String method;

	public CallbackNode(Event p, String m) {
		super(Kind.CALLBACK);
		purpose = p;
		method = m;
	}
	
	public boolean hasPurpose(Event e) {
		return purpose.equals(e);
	}
	
	public String getToolTip() {
		return "<b>Callback:</b> " + purpose + "<br>" + Node.htmlProtect(method);
	}
	
	public String toString() {
		return "Callback " + purpose;
	}
}
