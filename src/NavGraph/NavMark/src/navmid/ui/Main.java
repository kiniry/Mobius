package navmid.ui;
import java.io.IOException;

import javax.swing.JFrame;
import javax.swing.JScrollPane;

import navmid.graph.Node;
import navmid.graph.TransitionNode;
import navmid.parser.AnalysisFile;
import navmid.track.SerialConnection;
import navmid.track.Tracker;
import navmid.track.TrackerListener;

public class Main {
	public final static boolean debug = System.getProperty("DEBUG", "false") == "true";
	
	/**
	 * The entry point of the application. There is only one parameter: the name of the file.
	 * It can use several system properties:
	 * <ul>
	 * <li> SERIAL The name of the serial port used for tracking the midlet is given by the SERIAL property.
	 * <li> DOT The path to the dot executable used for node placement
	 * <li> DEBUG Set it to true to have more debug information.
	 * </ul>
	 * @param args an array containing the name of the results file.
	 * @throws IOException 
	 */
	public static void main(String[] args) throws IOException {
		Node.init();
		AnalysisFile af = new AnalysisFile(args[0],null);
		af.parse();
		TransitionNode.buildAll();
		if (debug) Node.dumpCurrentGraph(System.out);
	    GraphPanel panel = new GraphPanel(Node.graph(),debug ? null : Node.visible); //Node.visible

	    String serialPort = System.getProperty("SERIAL");
	    SerialConnection sc = new SerialConnection(serialPort);
	    sc.openConnection();
	    Tracker tr = new Tracker(sc, (TrackerListener) panel);
	    tr.track();
	    
	    JFrame frame = new JFrame("NavMark");
	    frame.getContentPane().add(new JScrollPane(panel));
	    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
	    frame.setSize(800, 600);
	    frame.setVisible(true);
	}

}
