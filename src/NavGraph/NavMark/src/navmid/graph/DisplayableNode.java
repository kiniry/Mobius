package navmid.graph;

import java.util.List;
import java.awt.Color;

import javax.annotation.CheckForNull;

/**
 * Class describing the screen contents which are the main nodes of the navigation graphs (other nodes are build artefacts).
 * @author piac6784
 *
 */
public class DisplayableNode extends ObjectNode {
	
	/**
	 * Default colors for state that corresponds to an lcdui screen contents.
	 */
	final static Color defaultColor = new Color(0xC0,0xff,0xC0);
	/**
	 * Default colors for state that do not correspond to a UI contents
	 */
	final static Color extremityColor = new Color(0xff,0xC0,0xC0);
	
	/**
	 * This enumeration defines the state represented by a Displayable object. Usually a screen contents
	 * but states have been added for special UI state before and after the midlet is run
	 * @author piac6784
	 *
	 */
	public enum DisplayableKind {
		/**
		 * Correspond to a MIDP Form 
		 */
		FORM,
		/**
		 * Correspond to a MIDP List 
		 */
		LIST,
		/**
		 * Correspond to a MIDP Alert 
		 */
		ALERT,
		/**
		 * Correspond to a MIDP TextBox
		 */
		TEXTBOX,
		/**
		 * Correspond to a MIDP Canvas (no support for MIDP2 GameCanvas yet because not event based)
		 */
		CANVAS,
		/**
		 * A Fake node representing the state before the start callback and after initialization
		 */
		START,
		/**
		 * A fake node representing the destroyed midlet.
		 */
		STOP,
		/**
		 * A fake node representing the initial state (before the midlet constructor is called).
		 */
		INIT
		};
	
	/**
	 * The kind of this displayable object
	 */
	public final DisplayableKind dpKind;
	/**
	 * 
	 */
	public final int matosId;
	/**
	 * Names of all the superclass of the object abstracted by this node.
	 */
	@CheckForNull
	public final List <String> classnames;
	
	/**
	 * A special node representing the entry of the graph.
	 */
	public static final DisplayableNode start = new DisplayableNode(DisplayableKind.START,-1, null);
	/**
	 * 
	 */
	public static final DisplayableNode stop = new DisplayableNode(DisplayableKind.STOP,-1, null);
	
	/**
	 * Builds a Displayable node
	 * @param dk the kind of this node.
	 * @param id the id used in the NavStatic result file
	 * @param classnames the list of names of classes extended by this object (and itself)
	 */
	public DisplayableNode(DisplayableKind dk, int id, List<String> classnames) {
		super(Kind.DISPLAYABLE);
		dpKind = dk;
		matosId = id;
		this.classnames = classnames;
	}
	
	/**
	 * Gives back all the command that may be registered on this displayable
	 * @return The list of abstract objects representing those commands.
	 */
	List<Node> getCommands() {
		return dests(Kind.COMMAND);
	}
	
	/**
	 * Gives back all the listener objects that may be registered on this displayable.
	 * @return the list of abstract objects representing those listeners
	 */
	List<Node> getListeners() {
		return dests(Kind.LISTENER);
	}
	
	public Color defaultColor() { 
		if (dpKind == DisplayableKind.START || dpKind == DisplayableKind.STOP) return extremityColor;
		return defaultColor;
	}
	
	public String toString() {
		return (dpKind + " " + origin ());
 	}
	
	public boolean isInstanceOf(String c) { 
		return classnames.contains(c);
	}
	
	public boolean isNotInstanceOf(String c) { 
		return ! classnames.contains(c);
	}
}
