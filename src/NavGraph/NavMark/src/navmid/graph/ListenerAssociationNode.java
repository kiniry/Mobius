package navmid.graph;

/**
 * A listener association node is a graph node created between a screen node and a class implementing
 * the event listener functionality (which may be used for several screen nodes). 
 * The role is represented by a {@link CallbackNode.Event}.
 * @author piac6784
 *
 */
public class ListenerAssociationNode extends Node {

	/**
	 * The event definining the role of the callback binding.
	 */
	final CallbackNode.Event event;
	
	/**
	 * Constructor with the role given to the binding. Private because it is called through the public
	 * static method  
	 * @param e
	 * @see #link(Node, Node, navmid.graph.CallbackNode.Event)
	 */
	private ListenerAssociationNode(CallbackNode.Event e) {
		super(Kind.LISTENER_ASSO);
		event = e;
	}
	
	/**
	 * Creates a callback binding between a Displayable and a listener with a given role. This means that events
	 * belonging to the role occuring on this displayable (or start stop nodes) will be treated by this listener.
	 * @param src the displayable abstract node that receives events,
	 * @param dst the listener abstract node that treats events,
	 * @param e the category of events treated.
	 */
	public static void link(Node src, Node dst, CallbackNode.Event e) {
		ListenerAssociationNode lan = new ListenerAssociationNode(e);
		src.linkTo(lan);
		lan.linkTo(dst);
	}
	
	/**
	 * Gives back the category of events treated by this association.
	 * @return the event
	 */
	public CallbackNode.Event event() { 
		return event;
	}
	
	public String toString() {
		return "LAN " + event;
	}
} 
