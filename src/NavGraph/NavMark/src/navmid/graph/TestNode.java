package navmid.graph;

import java.util.Set;

/**
 * Represents a parsable test on a path for which we can safely approximate the result.
 * This is used for pruning paths. So only false carries an information.
 * One side is a fixed approximation. The other is an element of the context.
 * 
 * This part must be refined as the previous version (navmid) could follow fields of
 * parameter objects which is not the case anymore. This is useful when the application
 * tests commands based on their name, not on their identity (stupid, I know).
 * @author piac6784
 *
 */
public class TestNode extends Node {
	final Set <Object> contents;
	final TestKind test;
	/**
	 * The position of the arguments in the context that is tested.
	 */
	final int position;
	
	/**
	 * This enumeration lists the tests handled by the analyzer and that can help to prune
	 * the list of paths extracted with the points-to analyis and the local path analysis.
	 * @author piac6784
	 *
	 */
	public enum TestKind {
		/**
		 * True if the arguments are equal objects.
		 */
		EQUAL, 
		/**
		 * True if the arguments are different objects.
		 */
		NOT_EQUAL,
		/**
		 * True if the parameter is an instance of the class defined by the string
		 * used as contents. 
		 */
		INSTANCE, 
		/**
		 * True if the parameter is NOT an instance of the class defined by the string used
		 * as contents
		 */
		NOT_INSTANCE, 
		/**
		 * Not solvable. Always safely considered as true.
		 */
		UNDEFINED 
	};

	/**
	 * Construct a new test node that will be the linked to a path. 
	 * @param test the kind of the test defined as an element of the enumeration.
	 * @param pos the position of the argument of the context filtered by this test.
	 * @param contents the contents of the test (the specific part)
	 */	
	public TestNode(TestKind test, int pos, Set <Object> contents) {
		super(Kind.GUARD);
		this.test = test;
		this.contents = contents;
		this.position = pos;
	}
	
	/**
	 * Construct a new test node that will be the linked to a path. 
	 * @param test the kind of the test defined as a string
	 * @param pos the position of the argument of the context filtered by this test.
	 * @param contents the contents of the test (the specific part)
	 */
	public TestNode(String test, int pos, Set <Object> contents) {
		super(Kind.GUARD);
		this.test= kindOf(test);
		this.contents = contents;
		this.position = pos;
	}
	
	/**
	 * Parse a string as givent back by Matos or navstatic and gives back an element of
	 * the enumeration.
	 * @param s A string representing a test.
	 * @return The equivalent formal kind.
	 */
	public TestKind kindOf(String s) {
		if (s.equals("==")) return TestKind.EQUAL;
		if (s.equals("!=")) return TestKind.NOT_EQUAL;
		if (s.equals("instanceOf")) return TestKind.INSTANCE;
		return TestKind.UNDEFINED;
	}
	
	/**
	 * Returns a new test node corresponding to the safe negation of the test represented by this
	 * TestNode.
	 * @return A new object corresponding to the negated test node.
	 */
	public TestNode negate() {
		return new TestNode(negateKind(test),position, contents);
	}
	
	/**
	 * Gives back the position of the argument of the callback filtered by this test.
	 * @return This position starting from 0.
	 */
	public int position() { 
		return position;
	}
	
	/**
	 * Method used to prune a path according to the context. If the test returns false then we
	 * can get rid of the path. Otherwise we keep it.
	 * @param n
	 * @return false if the test is NOT compatible with the argument and true otherwise
	 */
	public boolean ok(ObjectNode n) {
		switch(test) {
		case EQUAL:
			for(Object c:contents)
				if(n.equals(c)) return true;
			return false;
		case NOT_EQUAL :
			return true;
		case INSTANCE:
			for(Object c: contents)
				if (n.isInstanceOf((String) c)) return true;
			return false;
		case NOT_INSTANCE:
			for(Object c: contents)
				if (n.isNotInstanceOf((String) c)) return true;
			return false;	
		}
		return true;
	}
	
	
	/**
	 * The abstract negation of the test. Useful to preserve a correct approximation (as it is not correct
	 * to just used the negation of ok.
	 * @param t the kind of the test
	 * @return the kind corresponding to the negation.
	 */
	public static TestKind negateKind(TestKind t) {
		switch(t) {
		case EQUAL: return TestKind.NOT_EQUAL;
		case NOT_EQUAL : return TestKind.EQUAL;
		case INSTANCE : return TestKind.NOT_INSTANCE;
		case NOT_INSTANCE : return TestKind.INSTANCE;
		case UNDEFINED : return TestKind.UNDEFINED;
		default: return TestKind.UNDEFINED;
		}
	}
	
	public String getToolTip() {
		return ("<b>Test</b> " + position + " <b>" 
				+ test + "</b> " + Node.htmlProtect(contents.toString()));   
	}
	public String toString() {
		return "Test <" + test + "> " + contents;
	}
}

