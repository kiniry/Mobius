package inliner;

import java.util.HashMap;

import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.Type;

/**
 * Description of a callback method to modify. The restrictions are the following: 
 * <ul>
 * <li> At most two arguments.
 * <li> No primitive types for the arguments
 * <li> return type is void.
 * </ul>
 * The static method called at the beginning of the callback takes the same arguments as the 
 * callback (with the callback object itself) and is in the main class of the controller.
 * @author piac6784
 *
 */
public class CallbackDescription {
	/**
	 * Name of the interface defining the callback method.
	 */
	public final String classname;
	/**
	 * Name of the callback method.
	 */
	public final String methodname;
	/**
	 * Arguments of the callback methods in BCEL syntax
	 */
	public final Type [] args_types;
	/**
	 * Signature of the callback method in raw format (convenience field to avoid recomputation).
	 */
	public final String signature;
	/**
	 * Number of arguments of the callback (convenience field to avoid recomputation).
	 */
	public final int length;
	/**
	 * Name of method inserted. Its class is always Inliner.CONTROLLER_CLASS and its arguments
	 * are the same as the callback method
	 */
	public final String taggermethodname;
	
	private final static String LCDUI_PACKAGE = "javax.microedition.lcdui";
	private final static String DISPLAYABLE_TYPE = LCDUI_PACKAGE + ".Displayable";
	private final static String COMMAND_LISTENER_TYPE = LCDUI_PACKAGE + ".CommandListener";	
	private final static String ITEM_LISTENER_TYPE = LCDUI_PACKAGE + ".ItemCommandListener";
	private final static String COMMAND_TYPE = LCDUI_PACKAGE + ".Command";
	private final static String ITEM_TYPE = LCDUI_PACKAGE + ".Item";
	
	/**
	 * List of callbacks that may be modified with the name of the method inserted at their beginning.
	 */
	public static CallbackDescription [] callbacks;

	/**
	 * Map for memoizing the representation of types. 
	 */
	static private HashMap<String, ObjectType> type_rep = new HashMap<String,ObjectType> ();
	
	/**
	 * Given a class name gives back the BCEL representation of the corresponding type.
	 * @param classname the name of the class.
	 * @return the type representation.
	 */
	static private ObjectType type(String classname) {
		ObjectType r = type_rep.get(classname);
		if (r==null) {
			r = new ObjectType(classname);
			type_rep.put(classname,r);
		}
		return r;
	}
	
	/**
	 * Initialize the description of the types. Must be called once and could probably be replaced
	 * with a class initializer. 
	 */
	public static void init() {
		callbacks= new CallbackDescription [] {
				new CallbackDescription(COMMAND_LISTENER_TYPE,"commandAction", new String [] {COMMAND_TYPE, DISPLAYABLE_TYPE}, "callback1"),
				new CallbackDescription(ITEM_LISTENER_TYPE, "commandAction", new String [] {COMMAND_TYPE, ITEM_TYPE}, "callback2")
		};
	}

	/**
	 * Computes the raw method signature as it must be used . All the arguments must be objects and
	 * it cannot handle primitive types (not needed yet).
	 * @param args : the argument names as qualified classnames
	 * @return a string.
	 */
	private String method_subsignature(String [] args) {
		StringBuffer buf = new StringBuffer("(");
		for(String arg: args) {
			buf.append("L");
			buf.append(arg.replace('.', '/'));
			buf.append(';');
		}
		buf.append(")V");
		return buf.toString();
	}
	
	/**
	 * Builds a callback description and usually used only here.
	 * @param classname The name of the callback class
	 * @param methodname The name of the callback methods
	 * @param argsnames its arguments (objects)
	 * @param taggermethodname The name of the tagger method called with same arguments (but static)
	 */
	private CallbackDescription(String classname, String methodname, String [] argsnames, 
							   String taggermethodname) {
		this.classname = classname;
		this.methodname = methodname;
		this.taggermethodname = taggermethodname;
		length = argsnames.length;
		args_types = new Type [argsnames.length+1];
		args_types[0] = type(classname);
		for(int i=0; i < argsnames.length; i++) args_types[i+1] = type(argsnames[i]);
		signature = method_subsignature(argsnames);
	}
}
	
