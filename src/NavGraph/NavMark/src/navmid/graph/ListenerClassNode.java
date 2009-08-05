package navmid.graph;

/**
 * This node represents an implementation of a listener node. It is the destination of Listener
 * nodes representing actual instance and contains the description of callbacks.
 * @author piac6784
 *
 */
public class ListenerClassNode extends Node {
	/**
	 * The fully qualified name of the class described by this node.
	 */
	String clazz;
	
	/**
	 * Constructor requires a mandatory classname used to find the association with {@link ListenerNode}
	 * @param clazz the name of the class represented by this node.
	 */
	public ListenerClassNode(String clazz) {
		super(Kind.LISTENER_CLASS);
		this.clazz = clazz;
	}
	
	public String toString() {
		return "Class " + clazz;
	}
}
