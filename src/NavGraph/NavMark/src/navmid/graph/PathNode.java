package navmid.graph;

/**
 * Represents a path in a callback. It is characterized by its sons which are action nodes and tests.
 * @author piac6784
 *
 */
public class PathNode extends Node {
	
	/**
	 * The constructor specifies nothing but the kind of the node.
	 */
	public PathNode() {
		super(Kind.PATH);
	}
	
	public String toString() { return "Path"; }
}
