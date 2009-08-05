package navstatic.analyze;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import soot.SootClass;
import soot.SootMethod;

public class CallbackAnalysis {
	final Context context;
	final Map<SootMethod,PathAnalysis> results;

	
	public CallbackAnalysis(Context context)  {
		this.context = context;
		results = new HashMap<SootMethod, PathAnalysis> ();
		for (SootMethod callbackMethod : context.rules.callbackMethods) analyze(callbackMethod);
	}
	
	private void analyze(SootMethod callbackMethod) {
		SootClass itf = callbackMethod.getDeclaringClass();
		String subsignature = callbackMethod.getSubSignature();
		List <SootClass> support =
			itf.isInterface() ? context.hierarchy.getImplementersOf(itf) : context.hierarchy.getDirectSubclassesOf(itf);
		for(SootClass implClass: support) {
			try {
				SootMethod implMethod = implClass.getMethod(subsignature);
				analyzeCallback(implMethod,itf);
			} catch (RuntimeException e) { System.out.println(e.getMessage());}
		}
	}
	
	
	private void analyzeCallback(SootMethod meth, SootClass supportItf) {
		PathAnalysis pa = new PathAnalysis(context, meth, supportItf);
		results.put(meth, pa);
	}
	

	public void dump(PrintStream out) {
		for(Map.Entry<SootMethod, PathAnalysis> entry : results.entrySet()) {
			SootMethod meth = entry.getKey();
			PathAnalysis pa = entry.getValue();
			out.println("<callback method=\""  
					+ Explorer.htmlProtect(meth.getName()) 
					+ "\" class=\"" + Explorer.htmlProtect(meth.getDeclaringClass().toString())
					+ "\" extends=\"" + Explorer.htmlProtect(pa.supportItf.toString())
					+ "\">");
			pa.dump(out);
			out.println("</callback>");
		}
	}
}
