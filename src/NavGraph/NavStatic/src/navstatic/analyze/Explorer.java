package navstatic.analyze;

import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import soot.PackManager;
import soot.SootClass;
import soot.SootMethod;
import soot.SceneTransformer;
import soot.Transform;

public class Explorer extends SceneTransformer {
	/**
	 * The name of the global pack where the transformation is inserted.
	 */
	final static String PACK_NAME = "wjtp";
	/**
	 * The name of the transformation.
	 */
	final static String PHASE_NAME = "navstatic";
	/**
	 * The options of the transformation.
	 */
	final static String PHASE_OPTION = "enabled output";
	
	@SuppressWarnings("unchecked")
	@Override
	protected void internalTransform(String arg0, Map arg1) {
		String fileout = (String) arg1.get("output");
		PrintStream out;
		if (fileout != null) {
				try {
					out = new PrintStream(fileout);
				} catch (FileNotFoundException e) {
					System.out.println("Cannot open " + fileout + ". I use stdout instead.");
					out = System.out;
				}
		} else out = System.out;
		Context context = new Context();
		CallbackAnalysis cb = new CallbackAnalysis(context);
		solveConstructors(context);
		CallAnalysis ca = new CallAnalysis(context);
		out.println("<root>\n<midlet>");
		context.dump(out);
		ca.dump(out);
		cb.dump(out);
		out.println("</midlet>\n</root>");
	}
	
	/**
	 * Transform constructor rules (that say that the base argument of each 
	 * constructor for a given class and subclasses must be tracked) into a regular call rule
	 * @param context The global analysis context. Contains the set of rules.
	 */
	private void solveConstructors(Context context) {
		ArrayList <Integer> arg_zero = new ArrayList <Integer> ();
		arg_zero.add(0);
		for(ConstructorRule c: context.rules.constructorRules) {
			String name = c.name;
			List <SootClass> implems = context.hierarchy.getSubclassesOf(c.clazz);
			for(SootClass clazz: implems) {
				for(SootMethod m: clazz.getMethods()) {
					if (m.getName().equals("<init>")) {
						CallRule rule = new CallRule(name, m, arg_zero);
						context.rules.callRules.add(rule);
					}
				}
			}
		}
	}

	/**
	 * Gives back the argument string with all the character that may be confused by HTML escaped.
	 * @param text the text to escape
	 * @return a string that can be put in an HTML fragment.
	 */
	public static String htmlProtect(String text) {
		if (text==null) return "";
		if (text.indexOf('<') >= 0 || text.indexOf('>') >= 0 || text.indexOf('"') >= 0 || text.indexOf('&') >= 0)
			return (text.replaceAll("&","&amp;").replaceAll("<","&lt;").replaceAll(">","&gt;").replaceAll("\\\"","&quot;"));
		else return text;
	}
	
	/**
	 * Main entry point
	 * @param args. The arguments are given to SOOT which interpret them. 
	 * Nothing is done at that level. Use phase options to convey values and do not forget to
	 * declare those options.
	 */
	public static void main(String[] args) {
		Transform trf = new Transform(PACK_NAME + "." + PHASE_NAME, new Explorer());
		trf.setDeclaredOptions(PHASE_OPTION);
		PackManager.v().getPack(PACK_NAME).add(trf);
		soot.Main.main(args);
	}
}
