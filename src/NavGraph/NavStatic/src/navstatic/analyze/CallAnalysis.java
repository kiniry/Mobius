package navstatic.analyze;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Iterator;

import soot.Local;
import soot.PointsToSet;
import soot.SootMethod;
import soot.Value;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.toolkits.callgraph.Edge;
import soot.tagkit.BytecodeOffsetTag;

/**
 * Argument analysis for tracked methods (SRM and setters usually).
 * @author piac6784
 *
 */
public class CallAnalysis {
	
	/**
	 * List containing the results with one object per rule. 
	 */
	final ArrayList<CallResult> callResults;
	final private Context context;

	/**
	 * The constructor performs the analysis and prepare the result.
	 * @param context: the context object for the midlet.
	 */
	public CallAnalysis(Context context)  {
		this.context = context;
		callResults = new ArrayList<CallResult>();
		for(CallRule rule : context.rules.callRules) analyze(rule);
	}

	/**
	 * Analyze a given rule and adds the result to the [callResults] list.
	 * @param rule
	 */
	private void analyze(CallRule rule) {
		SootMethod meth = rule.method;
		for(Iterator<Edge> it = context.cg.edgesInto(meth); it.hasNext();) {
			Edge edge = it.next();
			SootMethod caller = edge.src();
			Stmt stmt = edge.srcStmt();
			InvokeExpr ie = stmt.getInvokeExpr();
			ArrayList <AbsValue> row = new ArrayList <AbsValue> ();
			for(Integer pos : rule.args) {
				Value arg = 
					(pos == 0 && ie instanceof InstanceInvokeExpr)
					? ((InstanceInvokeExpr) ie).getBase() 
					: ie.getArg(pos - 1);
				if (arg instanceof Local) {
					PointsToSet pts = context.pag.reachingObjects((Local) arg);
					AbsValue values = PointstoExplorer.contents(context, pts);
					row.add(values);
				} else if (arg instanceof StringConstant){
					row.add(new AbsValue.AbsString(((StringConstant) arg).value));
				} else if (arg instanceof IntConstant){
					row.add(new AbsValue.AbsInteger(((IntConstant) arg).value));
				} else {
					System.err.println("ARGUMENT: " + arg.getClass());
					row.add(null);
				}
			}
			CallResult result = new CallResult(rule.name, caller, stmt , meth, row);
			callResults.add(result);
		}
	}
	
	public void dump(PrintStream out) {
		for(CallResult result: callResults) {
			BytecodeOffsetTag tag = (BytecodeOffsetTag) result.stmt.getTag("BytecodeOffsetTag");
			int offset = (tag == null) ? -1 : tag.getBytecodeOffset(); 
			MarkTag mtag = (MarkTag) result.stmt.getTag("MarkTag");
			String markAttribute =
				(mtag==null) ? "" : ("mark=\"" + mtag.getMark() + "\" ");
			out.println("<args id=\"" + result.name +
					"\" orig=\"" + Explorer.htmlProtect(result.caller.getBytecodeSignature()) + 
					"\" offset=\"" + offset + "\" " + markAttribute +
					"target=\"" + Explorer.htmlProtect(result.callee.getName()) + "\">");
			for(AbsValue arg : result.args) {
				if (arg==null) out.println("<unknown/>");
				else out.println("  " + arg);
			}
			out.println("</args>");
		}		
	}
}
