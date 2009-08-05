package navstatic.analyze;

import java.util.ArrayList;

import soot.SootMethod;

public class CallRule {
	final String name;
	final SootMethod method;
	final ArrayList<Integer> args;
	
	public CallRule(String name, SootMethod method, ArrayList<Integer> args) {
		this.name=name;
		this.method=method;
		this.args=args;
	}
}
