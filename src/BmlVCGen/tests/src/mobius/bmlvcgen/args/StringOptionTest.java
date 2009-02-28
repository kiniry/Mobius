package mobius.bmlvcgen.args;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import mobius.bmlvcgen.args.Option.Arity;

import org.junit.Test;

/**
 * Tests of StringOption class.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class StringOptionTest {
	/**
	 * Default value should be 'null'.
	 */
	@Test
	public void testDefaultValue() {
		assertNull("Default value should be null",
				new StringOption('x').getValue());
	}
	
	/**
	 * StringOptions should have a mandatory argument
	 */
	@Test
	public void testArity() {
		assertEquals("Arity is invalid", 
				Arity.REQUIRED_ARGUMENT, 
				new StringOption('x').getArity());
	}
	
	/**
	 * Check if value is changed by setValue().
	 */
	@Test
	public void testSetValue() {
		final StringOption o = new StringOption('x');
		o.setValue("xyz");
		assertEquals("Value not changed", "xyz", o.getValue());
	}
}
