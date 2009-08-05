package navmid.graph;

import java.util.HashMap;
import java.util.Map;

/**
 * Represents an action in a midlet (either changing the current screen or performing a Security Relevant Method).
 * @author piac6784
 *
 */
public class ActionNode extends Node {
	/**
	 * Enumeration describing the kind of action node considered.
	 *
	 */
	public enum ActionKind { SETDISPLAY, CONNECT };
	
	/**
	 * The program point where this action occurs
	 */
	public String programPoint = null;
	
	/**
	 * A global map to find an action knowing its associated program point.
	 */
	private final static Map<String,ActionNode> programPointToAction = new HashMap<String,ActionNode> ();

	/**
	 * The kind of the node
	 */
	final ActionKind kind;
	
	/**
	 * Declares a new action node
	 * @param kind the kind of action represented.
	 */
	public ActionNode(ActionKind kind) {
		super(Kind.ACTION);
		this.kind = kind;
	}
	
	/**
	 * Defines the program point associated to this node.
	 * @param method the signature of the method
	 * @param offset the bytecode offset
	 */
	public void set_origin(String method, int offset) { 
		String key = "" + offset + "@" + method;
		System.err.println("Register " + key);
		programPointToAction.put(key, this);
	}

	/**
	 * Finds the action node associated to a given program point
	 * @param key the program point
	 * @return the action node found or null.
	 */
	public static ActionNode getAction(String key) { return programPointToAction.get(key); }	
	
	public String toString () {
		return "Action " + kind;
	}
}
