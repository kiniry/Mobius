// Tests parsing depends clauses

public class ParseDependsBad {

	//@ public model boolean b;

	boolean bb,bbb;

	//@ depends b <- bb,bbb;

	//@ depends bb <- bb; // program variable

	//@ depends x <- bb; // non-existent variable

	//@ depends b <- x; // depends on non-existent variable

	void m();
}
