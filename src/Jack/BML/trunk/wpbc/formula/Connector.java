/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public interface Connector {
	
	public static final byte AND = 1; // "&& ";
	public static final byte OR = 2; //"||";
	public static final byte NOT = 3; //"!";
	public static final byte IMPLIES = 4; //"==>";
	public static final byte EQUIV = 5; //"<==>";
	
}
