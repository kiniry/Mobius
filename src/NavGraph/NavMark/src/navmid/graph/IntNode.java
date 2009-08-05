package navmid.graph;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;


/**
 * Represents the potential values of an integer variable used as an attribute to an 
 * abstract object. The key is the name of the attribute.
 * @author piac6784
 *
 */
public class IntNode extends Node {
	final String key;
	final Set <Integer> values;
	
	/**
	 * Construct a new attribute associated to <code>key</code> with no initial value.
	 * @param key the identification of the attribute usually local to the origin object.
	 */
	public IntNode(String key) {
		super(Kind.INTEGER);
		this.key = key;
		values = new HashSet <Integer>();
	}
	
	/**
	 * Add a new potential value to the attribute.
	 * @param i the value added.
	 */
	public void add(Integer i) { values.add(i); }
	
	/**
	 * Adds a collection of new potential values to the attribute
	 * @param col the collection added.
	 */
	public void add(Collection <Integer> col) {values.addAll(col); }
	
	/**
	 * Gets the integer attribute of name key associated to the node node.
	 * @param node The node that carries the attribute
	 * @param key The name of the attribute
	 * @return The corresponding IntegerNode if it exists.
	 */
	public static IntNode get(Node node, String key) {
		List <Node> attrs = node.dests(Kind.INTEGER);
		for (Node attr_raw : attrs) {
			IntNode attr = (IntNode) attr_raw;
			if (attr.key.equals(key)) return attr;
		}
		IntNode attr = new IntNode(key);
		node.linkTo(attr);
		return attr;
	}
	
	public String toString(){
		return key + ":" + values ;
	}
		
	public boolean isInstanceOf(String c) { return c.equals("java.lang.Integer") || c.equals("java.lang.Object"); }
}
