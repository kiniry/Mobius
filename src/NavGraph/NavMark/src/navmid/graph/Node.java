package navmid.graph;
import java.awt.Color;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.umd.cs.findbugs.annotations.NonNull;

/**
 * The basic class for nodes. It is subclassed by actual graph members but defines the main
 * behaviours of a graph node and implements the notion of graph.
 * @author piac6784
 *
 */
public class Node {
	/**
	 * An enumeration listing the kind (purpose) of graph nodes. This is more or less redundant with the subclass
	 * of Node but allow easy filtering (see for example {@link Node#dests(Kind)} 
	 * @author piac6784
	 *
	 */
	public enum Kind {
		/**
		 * A virtual kind used in node filtering (never used as the kind of a node). 
		 */
		ANY, 
		/**
		 * Special kind for the root of the graph.
		 */
		GRAPH, 
		/**
		 * The abstraction of a MIDP displayable object (screen contents).
		 */
		DISPLAYABLE, 
		/**
		 * Abstraction of a software button 
		 */
		COMMAND, 
		/**
		 * Abstraction of a form element.
		 */
		ITEM, 
		/**
		 * Abstraction of the association between a displayable object (or item) and a callback
		 */
		LISTENER_ASSO, 
		/**
		 * Abstraction of a listener object
		 */
		LISTENER, 
		/**
		 * The listener class itself
		 */
		LISTENER_CLASS, 
		/**
		 * A callback method in a listener class.
		 */
		CALLBACK, 
		/**
		 * An abstraction of an execution path in a callback method.
		 */
		PATH, 
		/**
		 * Guards (tests) along the path in a callback method. 
		 */
		GUARD, 
		/**
		 * Actions taken.along a path (call to a SRM or displaying a new screen).
		 */
		ACTION, 
		/**
		 * Transitions from one displayable to another displayable
		 */
		TRANSITION, 
		/**
		 * An integer attribute of an object abstraction
		 */
		INTEGER, 
		/**
		 * A string attribute of an object abstraction.
		 */
		STRING 
	}; 
	/**
	 * All the nodes that are source of a graph transition to this node
	 */
	private final ArrayList <Node> origins;
	/**
	 * All the nodes that are destination of a graph transition from this node
	 */
	protected final ArrayList <Node> dests;
	/**
	 * An id unique to this node and that can be used to represent it.
	 */
	public final int unique_id;
	/**
	 * The kind of this node (usually implies the exact subclass of the node).
	 */
	private Kind kind;
	
	/**
	 * A list of kinds that are displayed.
	 */
	public static final Set<Kind> visible = new HashSet<Kind> ();;
	{
		visible.add(Kind.DISPLAYABLE);
		visible.add(Kind.COMMAND);
		visible.add(Kind.ACTION);
		visible.add(Kind.TRANSITION);
		visible.add(Kind.ITEM);
		visible.add(Kind.INTEGER);
	}
	
	/**
	 * A unique node that represents the root of the graph. All nodes have this node as origin.
	 */
	
	/*@ invariant current_graph == null || current_graph.kind == Kind.GRAPH */
	static private Node current_graph;
	
	/**
	 * A counter for generating unique ids. 
	 */
	static private int counter = 0;
	

	/**
	 * Create a new node with a unique id and an initial empty lists of linked nodes. The
	 * node is registered in the current graph.
	 * The constructor is never called directly (an exception is the graph node). 
	 * Only specific kind of nodes are created. This is controlled by the subclasses.
	 * @param kind
	 */
	/*@ requires kind != Kind.ANY; */
	protected Node(Kind kind) {
		this.kind = kind;
		unique_id =  counter++;
		origins = new ArrayList <Node>();
		dests = new ArrayList <Node>();
		if (kind != Kind.GRAPH) current_graph.linkTo(this);
	}
	
	/**
	 * Initialize the graph with a unique graph node. Called once, but could also be used to
	 * reset the graph (giving it a new anchor). 
	 */
	public static void init() {
		current_graph = new Node(Kind.GRAPH);
	}
	
	/**
	 * Gives back the graph identified by its root node.
	 * @return the root of the graph
	 */
	public static Node graph() { return current_graph; }
	
	/**
	 * Gives back the kind defining the purpose of this node in the graph. 
	 * @return the kind.
	 */
	public Kind kind() { return kind; }
	
	/**
	 * Establish a transition to another node, with this node as origin and the other as destnation.
	 * @param n The destination node of the link.
	 */
	public void linkTo(Node n) {
		dests.add(n);
		n.origins.add(this);
	}
	
	/**
	 * Remove a node from the graph. All the nodes linked to it are modified to reflect the changes in the
	 * links.
	 */
	public void delete() {
		for(Node t: origins(Kind.ANY)) { t.dests.remove(this); }
		for(Node t: dests(Kind.ANY)) { t.origins.remove(this); }
	}
	

	/**
	 * Gives back all the nodes that are destinations of a transition starting from this node filtered 
	 * on a given kind.
	 * @param kind The filtered kind or ANY if there is no filtering.
	 * @return A list of nodes.
	 */
	public List<Node> dests(Kind kind) {
		if(kind==Kind.ANY) return dests;
		else {
			ArrayList <Node> result = new ArrayList <Node>();
			for(Node n: dests) { if(n.kind==kind) result.add(n); }
			return result;
		}
	}
	
	/**
	 * Gives back all the nodes that are sources of a transition ending to this node filtered 
	 * on a given kind.
	 * @param kind The filtered kind or ANY if there is no filtering.
	 * @return A list of nodes.
	 */
	public List<Node> origins(Kind kind) {
		if(kind==Kind.ANY) return origins;
		else {
			ArrayList <Node> result = new ArrayList <Node>();
			for(Node n: origins) { if(n.kind==kind) result.add(n); }
			return result;
		}
	}
	
	/**
	 * Gives back all the nodes of the graph of a given kind (or all the nodes if the kind is ANY).
	 * @param kind The filtered kind or ANY if there is no filtering.
	 * @return A list of nodes of the given kind or all the nodes if ANY was used.
	 */
	public static List <Node> all(Kind kind) {
		return current_graph.dests(kind);
	}
	
	/**
	 * Debug function used to print the graph on an output stream. We print for each node
	 * its short content (toString) and the contents of the nodes it is linked to.
	 * @param out The printstream on which the result is printed.
	 */
	public static void dumpCurrentGraph(PrintStream out) {
		for(Node n: current_graph.dests(Kind.ANY)) {
			out.println(n.unique_id + ": " + n);
			for(Node d: n.dests(Kind.ANY)) out.println("-->" + d.unique_id + ": " + d);
			out.println();
		}
	}

	/**
	 * The local private color 
	 */
	private Color color = null;

	/**
	 * Gives back the default color associated to the class of objects. This method is usually overridden
	 * by subclasses. It is recommended to use soft default color and use bright colors for temporary events.
	 * 
	 * @return this default color
	 */
	public Color defaultColor () { return Color.white; }
	
	/**
	 * The background color as queried by the graph displayer. Gives back the default color associated to
	 * the node class unless a temporary color has been set for this specific node.
	 * @return The color of the background of the cell representing the node.
	 */
	public Color bgColor() {
		if(color != null) return color;
		return defaultColor();
	}
	
	/**
	 * Set the local temporary color associated to this object
	 * @param color An AWT color object or null to reset to the default color.
	 */
	public void setColor(Color color) { this.color = color; }
	
	/**
	 * A utility to transform an AWT color in a string coding the color in classical HTML format
	 * also usable by dot.
	 * @param color an AWT color representation as used internally.
	 * @return a string usable to represent the color in dot.
	 */
	public static String colorName(Color color) {
		return String.format("#%1$02x%2$02x%3$02x", color.getRed(), color.getGreen(), color.getBlue());
	}
	
	/**
	 * A method to generate a dot file from the graph. The file is usually processed by dot to generate
	 * a postscript file. This is a debug method. 
	 * @param out
	 * @param restriction The set of nodes we went to make visible. Use null for no restriction. The other
	 * sensible value is {@link Node#visible}
	 */
	public static void dumpToDot(PrintStream out, Set<Kind> restriction) {
		out.println("digraph navmid {");
		out.println("size=\"100,100\";");
		for(Node n: current_graph.dests(Kind.ANY)) {
			if (restriction == null || restriction.contains(n.kind)) {
				String label = n.toString();
				if (label.length() > 25) label = label.substring(0,21) + "... ";
				out.println("N" + n.unique_id + "[ label=\"" + label + "\",fillcolor=\"" + colorName(n.bgColor()) + "\",style=\"filled\"];");
			}	
		}
		
		for(Node n: current_graph.dests(Kind.ANY)) {
			if (restriction != null && ! restriction.contains(n.kind)) continue;
			for(Node d: n.dests(Kind.ANY)) 
				if (restriction == null || restriction.contains(d.kind))
				out.println( "N" + n.unique_id + " -> N" + d.unique_id + ";");
		}
		out.println("}");
	}
		
	/**
	 * A utility function that escapes all the potentially interpretable HTML characters so that it
	 * can be displayed in a browser without problem. 
	 * @param s the original string.
	 * @return the escaped string.
	 */
	@NonNull
	public static String htmlProtect(String s) {
		if (s==null) return "";
		if (s.indexOf('<') >= 0 || s.indexOf('>') >= 0 || s.indexOf('"') >= 0 || s.indexOf('&') >= 0)
			return (s.replaceAll("&","&amp;").replaceAll("<","&lt;").replaceAll(">","&gt;").replaceAll("\\\"","&quot;"));
		else return s;
	}


	/**
	 * Gives back the text in HTML format that is displayed in the tooltip associated to the node. 
	 * This is usually a longer version of what is given back by toString.
	 * @return The text displayed.
	 */
	public String getToolTip() { return htmlProtect(toString()); }
}
