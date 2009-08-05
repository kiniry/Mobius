package navmid.graph;

/**
 * A listener node is an abstraction of a dynamic object implementing an event listener. Its class is 
 * represented by a {@link ListenerClassNode}. It is the class that contains the callbacks.
 * There is usually one single instance of each listener class and so a one to one correspondence between
 * ListenerNode and ListenerClassNode objects but this is not a MIDP requirement. 
 * @author piac6784
 *
 */
public class ListenerNode extends Node {
	/**
	 * The name of the class of this listener (will define the association with a ListenerClassNode)
	 */
	public final String clazz;
	/**
	 * The id used in the result file.
	 */
	public final int matosId;
	
	/**
	 * Constructor for a node representing an instance of event listeners with the class (and so the behaviour)
	 * it implements and the object key form navstatic or Matos.
	 * @param c the fully qualified name of the class
	 * @param id the matos identifier as an integer.
	 */
	public ListenerNode(String c, int id) {
		super(Kind.LISTENER);
		matosId = id;
		clazz = c;
	}

	public String toString() {
		return "Listener " + matosId;
	}
}
