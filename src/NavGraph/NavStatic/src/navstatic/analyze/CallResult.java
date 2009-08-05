package navstatic.analyze;

import java.util.ArrayList;

import soot.SootMethod;
import soot.jimple.Stmt;

public class CallResult {
	final public String name;
	final public SootMethod caller;
	final public Stmt stmt;
	final public SootMethod callee;
	final public ArrayList<AbsValue> args;
	
	public CallResult(String name, SootMethod caller, Stmt stmt, SootMethod callee, ArrayList<AbsValue> args) {
		this.name = name;
		this.caller = caller;
		this.stmt = stmt;
		this.callee = callee;
		this.args = args;
	}
}
