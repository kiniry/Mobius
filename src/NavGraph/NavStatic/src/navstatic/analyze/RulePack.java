package navstatic.analyze;

import java.util.HashSet;
import java.util.Set;

import soot.SootMethod;

public class RulePack {
	final public Set <CallRule> callRules;
	final public Set <ConstructorRule> constructorRules;
	final public Set <SootMethod> trackedMethods;
	final public Set <SootMethod> setterMethods;
	final public Set <SootMethod> callbackMethods;

	public RulePack() {
		callRules = new HashSet <CallRule>();
		constructorRules = new HashSet  <ConstructorRule>();
		trackedMethods = new HashSet <SootMethod> ();
		setterMethods = new HashSet <SootMethod> ();
		callbackMethods = new HashSet <SootMethod> ();
	}
}
