package mobius.bmlvcgen.args;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/**
 * Option class used for testing the parser.
 * It receives an array of strings and checks
 * if calls to setValue() matched values from
 * the list.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class MockOption extends AbstractOption {
	private String[] expected = new String[0];
	private int pos;
	
	/**
	 * Constructor.
	 * @param shortName Short name.
	 * @param arity Arity.
	 */
	public MockOption(
			final char shortName,
			final Arity arity) {
		super(shortName, arity);
	}

	/**
	 * Constructor.
	 * @param longName Long name.
	 * @param arity Arity.
	 */
	public MockOption(
			final String longName,
			final Arity arity) {
		super(longName, arity);
	}
	
	/**
	 * Constructor.
	 * @param shortName Short name.
	 * @param longName Long name.
	 * @param arity Arity.
	 */
	public MockOption(
			final char shortName,
			final String longName,
			final Arity arity) {
		super(shortName, longName, arity);
	}

	/**
	 * Set list of expected values.
	 * Calling this method resets any previous calls.
	 * @param values Expected values. 
	 * This array may contain null values.
	 */
	public void expect(final String... values) {
		pos = 0;
		expected = values;
	}
	
	/** {@inheritDoc} */
	public void setValue(final String value) {
		if (pos >= expected.length) {
			fail("No more values were expected");
		} else {
			assertEquals("Invalid option value", 
					expected[pos], value);
			pos = pos + 1;
		}
	}
}
