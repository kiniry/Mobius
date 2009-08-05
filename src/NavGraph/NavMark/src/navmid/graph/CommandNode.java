package navmid.graph;

import java.awt.Color;

/**
 * This class describes an abstract command object allocated at a given point. 
 * @author piac6784
 *
 */
public class CommandNode extends ObjectNode {
	/**
	 * Identifies the object in the navstatic or matos result file 
	 */
	public final int matosId;
	/**
	 * Create a new command node
	 * @param id unique identification of the node by its MATOS or Navstatic id
	 */
	public CommandNode(int id) {
		super(Kind.COMMAND);
		matosId=id;
	}
	
	public boolean isInstanceOf(String c) { return c.equals("javax.microedition.lcdui.Command") || c.equals("java.lang.Object"); }
	
	public Color bgColor() {
		if(identified) return Color.cyan;
		return Color.white;
	}
	
	public String toString() {
		return ("Command " + origin());
	}
}
