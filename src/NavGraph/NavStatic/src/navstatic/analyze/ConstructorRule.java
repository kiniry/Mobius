package navstatic.analyze;

import soot.SootClass;

public class ConstructorRule {
	final String name;
	final SootClass clazz;
	
	public ConstructorRule(String name, SootClass clazz) {
		this.name = name;
		this.clazz = clazz;
	}
}
