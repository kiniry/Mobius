package navstatic.analyze;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;

import navstatic.parser.Parser;
import soot.Hierarchy;
import soot.PointsToAnalysis;
import soot.Scene;
import soot.SootClass;
import soot.jimple.toolkits.callgraph.CallGraph;

/**
 * Context for the analysis. It keeps pointer on basic Soot services and on global tables for rules 
 * (what must be done) and objects (what has been discovered).
 * @author piac6784
 *
 */
public class Context {

	/**
	 * The current scene. Soot context. It is the root point to access classes and global analysis on 
	 * these (callgraph, pointsto, other).
	 */
	final Scene scene;
	/**
	 * The current global points-to analysis (using Spark).
	 */
	final PointsToAnalysis pag;
	/**
	 * The current call graph
	 */
	final CallGraph cg;
	/**
	 * The class hierarchy of the midlet.
	 */
	final Hierarchy hierarchy;
	/**
	 * The set of analysis rules.
	 */
	final RulePack rules;
	/**
	 * All the abstract objects discovered during the analysis.
	 */
	final Map<Integer, SootClass> abstractObjects;

	/**
	 * The constructor initializes the Soot objects and parse the set of rules.
	 */
	public Context() {
		scene = Scene.v();
		pag = scene.getPointsToAnalysis();
		cg = scene.getCallGraph();
		hierarchy = scene.getActiveHierarchy();
		Parser parser = new Parser();
		rules = parser.parse(scene);
		abstractObjects = new HashMap<Integer,SootClass>();
	}
	

	/**
	 * Dump the global object table on the output stream
	 * @param out the output stream.
	 */
	public void dump(PrintStream out) {
		for(Map.Entry<Integer, SootClass> entry: abstractObjects.entrySet()) {
			out.println("<node id=\"" + entry.getKey() + "\">");
			SootClass c = entry.getValue();
			while(true) {
				out.println("  <class name=\"" + c + "\"/>");
				for(SootClass itf : c.getInterfaces())
					out.println("  <interface name=\"" + itf + "\"/>");
				if (c.hasSuperclass()) c=c.getSuperclass(); else break;
			}
			out.println("</node>");
		}
	}
	
}
