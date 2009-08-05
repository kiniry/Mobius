package navmid.ui;

import java.awt.Color;
import java.awt.Font;
import java.awt.event.MouseEvent;
import java.awt.geom.Point2D;
import java.awt.geom.Rectangle2D;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.swing.BorderFactory;
import javax.swing.ToolTipManager;
import javax.swing.border.Border;

import navmid.graph.Node;
import navmid.graph.ObjectNode;
import navmid.graph.Node.Kind;
import navmid.track.TrackerListener;

import org.jgraph.JGraph;
import org.jgraph.graph.AttributeMap;
import org.jgraph.graph.DefaultCellViewFactory;
import org.jgraph.graph.DefaultEdge;
import org.jgraph.graph.DefaultGraphCell;
import org.jgraph.graph.DefaultGraphModel;
import org.jgraph.graph.DefaultPort;
import org.jgraph.graph.GraphCell;
import org.jgraph.graph.GraphConstants;
import org.jgraph.graph.GraphLayoutCache;

/**
 * @author piac6784
 *
 */
public class GraphPanel extends JGraph implements TrackerListener {
	
	private static final long serialVersionUID = 1L;
	
	final Node root;
	/**
	 * The restriction on nodes displayed.
	 */
	final Set <Kind> restriction;
	/**
	 * Placement information for nodes
	 */
	final Map <Integer,Rectangle2D> nodeCoord;
	/**
	 * Placement information for edges.
	 */
	final Map <Long, List <Point2D>> edgeCoord;
	/**
	 * A map to maintain a one to one correspondance between graph nodes and their representation in jGraph.
	 */
	final Map <Integer, DefaultGraphCell> nodeCell;
	/**
	 * A map to maintain a one to one correspondance between links (from one node to another) and their
	 * representation in jgraph.
	 */
	final Map <Long, GraphCell> edgeCell;
	boolean debug = false;
	final static Border BorderUnseen = BorderFactory.createLineBorder(Color.black,1);
	final static Border BorderRecognised = BorderFactory.createLineBorder(Color.black,2);

	private static final int SCALE_X = 120;
	private static final int SCALE_Y = 80;
	
	/**
	 * An extension to the GraphCell defined by JGraph that handles ToolTips in HTML format.
	 * @author piac6784
	 *
	 */
	public static class ToolTipGraphCell extends DefaultGraphCell {
		private static final long serialVersionUID = 1L;
		
		final String tooltip;
		
		ToolTipGraphCell(String label, String tooltip) { 
			super(label); 
			this.tooltip = "<html>" + tooltip + "</html>";
		}
		public String getToolTipString() { return tooltip; }
	}
	
	/**
	 * Creates the panel displaying the graph restricted to a given set of cells. The root
	 * is explicitely given
	 * @param graphRoot  the root of the graph
	 * @param restriction the set of node kinds to display or null if everything is shown. 
	 */
	public GraphPanel(Node graphRoot, Set <Kind> restriction) {
		super(new DefaultGraphModel());
		ToolTipManager.sharedInstance().registerComponent(this);
		root = graphRoot;
		this.restriction = restriction;
		nodeCoord = new HashMap <Integer,Rectangle2D> ();
		edgeCoord = new HashMap <Long, List <Point2D>> ();
		
		nodeCell = new HashMap <Integer,DefaultGraphCell> ();
		edgeCell = new HashMap <Long, GraphCell> ();
		
		GraphLayoutCache view = new GraphLayoutCache(getModel(), new DefaultCellViewFactory());
		this.setGraphLayoutCache(view);

		doPlacement();
		
		List <GraphCell> cells = new ArrayList <GraphCell> ();
		Font font = new Font(Font.SANS_SERIF,Font.PLAIN,8);
		for(Node n: root.dests(Kind.ANY)) {
			if (restriction == null || restriction.contains(n.kind())) {
				String label = n.toString();
				if (debug) label = n + ": " + label;
				String shortLabel =	(label.length() > 45) ? label.substring(0,21) + "... " : label;
				DefaultGraphCell c = new ToolTipGraphCell(shortLabel,n.getToolTip());
				AttributeMap attributes = c.getAttributes();
				if (n instanceof ObjectNode) 
					GraphConstants.setBorder(attributes,((ObjectNode) n).isIdentified() ? BorderRecognised : BorderUnseen );
				else GraphConstants.setBorder(attributes, BorderUnseen);
				GraphConstants.setFont(attributes, font);
				GraphConstants.setBounds(attributes, nodeCoord.get(n.unique_id));
				GraphConstants.setOpaque(attributes,true);
				GraphConstants.setBackground(attributes, n.bgColor());
				cells.add(c);
				nodeCell.put(n.unique_id,c);
			}
		}
		for(Node n: root.dests(Kind.ANY)) {
			if (restriction != null && ! restriction.contains(n.kind())) continue;
			for(Node t: n.dests(Kind.ANY)) 
				if (restriction == null || restriction.contains(t.kind())) {
					DefaultEdge e = new DefaultEdge();
					DefaultPort pn = new DefaultPort();
					nodeCell.get(n.unique_id).add(pn);
					e.setSource(pn);
					DefaultPort pt = new DefaultPort();
					nodeCell.get(t.unique_id).add(pt);
					e.setTarget(pt);
					AttributeMap attributes = e.getAttributes();
					GraphConstants.setLineStyle(attributes, GraphConstants.STYLE_BEZIER);
					// GraphConstants.setRouting(attributes, GraphConstants.ROUTING_SIMPLE);
					GraphConstants.setPoints(attributes, edgeCoord.get(edge(n.unique_id,t.unique_id)));
					GraphConstants.setLineEnd(attributes, GraphConstants.ARROW_CLASSIC);
					GraphConstants.setEndFill(attributes, true);
					cells.add(e);
				}
		}
		GraphCell [] cellArray = cells.toArray(new GraphCell [0]);
		getGraphLayoutCache().insert(cellArray);
		
	}
	
	public String getToolTipText(MouseEvent event) {
		Object cell = getFirstCellForLocation(event.getX(), event.getY());
		if (cell instanceof ToolTipGraphCell) {
			return ((ToolTipGraphCell) cell).getToolTipString();
		}
		return null;
	}

	public void update(Node node) {
		Hashtable modification = new Hashtable();
		Hashtable map = new Hashtable ();
		GraphCell c =  nodeCell.get(node.unique_id);
		Color newColor = node.bgColor();
		if (node instanceof ObjectNode && ((ObjectNode) node).isIdentified() ) GraphConstants.setBorder(map,BorderRecognised);
		GraphConstants.setBackground(map, newColor);
		modification.put(c, map);	
		System.err.println("Updating " + node.unique_id + " " + c + " " + newColor);
		GraphLayoutCache glc = getGraphLayoutCache();
		glc.edit(modification,null,null,null);
		repaint();
	}
	
	/**
	 * Prints a raw dot file for placement. There is no labels as we are only interested in
	 * node placement.
	 * @param out The stream on which to print the dot file (usually a pipe).
	 * @param root The root of the graph
	 * @param restriction A set of kinds restricting the nodes that will be displayed (placement
	 * and display must use the same set).
	 */
	private void printDot(PrintStream out, Node root, Set<Kind> restriction) {
		out.println("digraph navmid {");
		String text;
		for(Node n: root.dests(Kind.ANY)) {
			if (restriction == null || restriction.contains(n.kind())) {
				text = "N" + n.unique_id;
				if (debug) System.err.println(n + ": " + text);
				out.println(text);
			}
		}
		for(Node n: root.dests(Kind.ANY)) {
			if (restriction != null && ! restriction.contains(n.kind())) continue;
			for(Node d: n.dests(Kind.ANY)) 
				if (restriction == null || restriction.contains(d.kind())) {
					text =  "N" + n.unique_id + " -> N" + d.unique_id + ";";
					if (debug) System.err.println(text);
					out.println(text);
				}
				
		}
		out.println("}");
	}
	
	/**
	 * Computes a unique id as a long for an edge using the id of the source and destination
	 * @param src the id of the source node,
	 * @param dst the id of the destination node.
	 * @return a long.
	 */
	static public Long edge(int src, int dst) {
		return Long.valueOf(((long) src << 32) + (long) dst);
	}
	
	/**
	 * Parses the output of a dot file processed with plain option. It extracts the placement
	 * of nodes and set the graph accordingly.
	 * @param in The stream to read the result file from.
	 */
	private void parseDot(BufferedReader in) {
		String [] line;
		try {
			while (true) {
				String input = in.readLine();
				if (input == null) break;

				line = input.trim().split("\\s+");
				if (debug) System.err.println(input);
				if (line.length == 0 || line[0].equals("stop")) break;
				if (line[0].equals("graph")) {
		//			width = Double.parseDouble(line[2]);
		//			height = Double.parseDouble(line[3]);
				} else if (line[0].equals("node")) {
					Integer node = Integer.valueOf(line[1].substring(1));
					double x = Double.parseDouble(line[2]) * SCALE_X;
					double y = Double.parseDouble(line[3]) * SCALE_Y;
					double w = Double.parseDouble(line[4]) * SCALE_X;
					double h = Double.parseDouble(line[5]) * SCALE_Y;
					Rectangle2D bounds = new Rectangle2D.Double(x - w / 2,y - h / 2,w,h);
					nodeCoord.put(node, bounds);
				} else if (line[0].equals("edge")) {
					int node1 = Integer.parseInt(line[1].substring(1));
					int node2 = Integer.parseInt(line[2].substring(1));
					Long edge = edge(node1,node2);
					int n = Integer.parseInt(line[3]);
					ArrayList <Point2D> pos = new ArrayList();
					for(int i = 0; i < n; i++) {
						double x = Double.parseDouble(line[4 + i * 2]) * SCALE_X;
						double y = Double.parseDouble(line[5 + i * 2]) * SCALE_Y;
						pos.add(new Point2D.Double(x,y));
					}
					edgeCoord.put(edge,pos);
				}
			}
		} catch (IOException e) {}
	}
	
	/**
	 * This method performs the placement of the nodes of the graph. It uses dot internally. 
	 */
	private void doPlacement() {
		Runtime rs = Runtime.getRuntime();
		try {
			String dotPath = System.getProperty("DOT", "dot");
			Process p = rs.exec(dotPath + " -Tplain");
			PrintStream out = new PrintStream(new BufferedOutputStream(p.getOutputStream()));
			printDot(out, root, restriction);
			out.close();
			BufferedReader in = new BufferedReader(new InputStreamReader(p.getInputStream()));
			parseDot(in);
			int r = p.waitFor();
			if (r != 0) { System.err.println("Placement problem. Is dot available ?"); }
		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
	}
}
