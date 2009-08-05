package navmid.graph;

import java.util.HashMap;
import java.util.Map;

import edu.umd.cs.findbugs.annotations.CheckForNull;

/**
 * An Object Node is a node of the graph corresponding to an abstraction of live Java objects. Usually these 
 * are the objects allocated at a given program point.
 * 
 * Finally an object is identified when it has been recognized by the tracker. This boolean can flip from
 * false to true but never from true to false.
 *  
 * @author piac6784
 *
 */
public class ObjectNode extends Node {
	
	/**
	 * This is a delegate and is not used directly.
	 * @param k
	 */
	protected ObjectNode(Kind k) { super(k); }
	
	/**
	 * A static map containing the translation between program points coded as strings and Object nodes.
	 */
	private final static Map<String,ObjectNode> programPointToObject = new HashMap<String,ObjectNode> ();
	
	/**
	 * The method name defining the program point 
	 */
	private String programPointMethod = null;
	
	/**
	 * The bytecode offset in the method defining the program point
	 */
	private int programPointOffset;
	
	
	/**
	 * Declares the program point associated to the node
	 * @param m the method signature.
	 * @param o the offset.
	 */
	public void set_origin(String m, int o) { 
		if (programPointMethod==null) {
			programPointMethod = m; 
			programPointOffset = o;
			String key = "" + programPointOffset + "@" + programPointMethod;
			System.err.println("Register " + key);
			programPointToObject.put(key, this);
		}; // else throw new RuntimeException("set_origin");
	}
	
	/**
	 * Gives back the program point as used by navmod
	 * @return the program point or null if not initialized.
	 */
	@CheckForNull
	public String origin() { return (programPointMethod == null) ? null : programPointMethod + "@" + programPointOffset; }
	
	/**
	 * Finds the object node associated to a given key if it has been registered
	 * @param key a program point coded in navmod format.
	 * @return The object node found or null.
	 */
	@CheckForNull
	public static ObjectNode getObject(String key) { return programPointToObject.get(key); }

	/**
	 * Boolean indicating if the object has been recognized during a test session.
	 */
	protected boolean identified = false;
	/**
	 * Used on object nodes usually to check if they represent instances of a given class.
	 * This is used to implement the instanceof test and must give back a correct approximation.
	 * @param c the name of the class.
	 * @return true only if it is an instance of this given class. 
	 */
	public boolean isInstanceOf(String c) { return true; }
	/**
	 * Used on object nodes usually to check if they represent instances of a given class.
	 * This is used to implement the instanceof test and must give back a correct approximation.
	 * @param c the name of the class.
	 * @return true only if it is an instance of this given class. 
	 */
	public boolean isNotInstanceOf(String c) { return true; }

	/**
	 * Called when a live instance of the object node has been identified in the execution of the midlet. 
	 */ 
	public void identify() { identified = true; }

	/**
	 * Indicates if a live instance of the object has been identified during the test session.
	 * @return true if identified, false otherwise.
	 */
	public boolean isIdentified() { return identified; }
	
}
