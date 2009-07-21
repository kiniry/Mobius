package mobius.bmlvcgen.args;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.lang.reflect.Method;

import mobius.bmlvcgen.args.Option.Arity;
import mobius.bmlvcgen.args.converters.Converter;
import mobius.bmlvcgen.args.converters.DefaultConverter;

import org.junit.Before;
import org.junit.Test;

/**
 * Tests for the SetterOption class.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class SetterOptionTest {
	private String expected;
	private boolean methodCalled;
	private Method m1;
	private Method m2;
	private Converter converter;
	
	public void m(final String value) {
		assertEquals("Wrong value passed to setter", 
				expected, value);
		methodCalled = true;
	}
	
	public void m() {
		methodCalled = true;
	}
	
	/** Initialization. */
	@Before
	public void setUp() throws Exception {
		methodCalled = false;
		m1 = this.getClass().getMethod("m");
		m2 = this.getClass().getMethod("m", String.class);
		converter = new DefaultConverter();
	}
	
	/**
	 * Method without parameters.
	 */
	@Test
	public void testWithoutParameters() {
		final SetterOption opt = 
			new SetterOption(this, m1, converter, null, 'x', 
					Arity.NO_ARGUMENT);
		opt.setValue(null);
		assertTrue("Method was not invoked", methodCalled);
	}
	
	/**
	 * Method with paramer.
	 */
	@Test
	public void testWithParameter() {
		final SetterOption opt = 
			new SetterOption(this, m2, converter, null, 'x', 
					Arity.REQUIRED_ARGUMENT);
		expected = "test";
		opt.setValue("test");
		assertTrue("Method was not invoked", methodCalled);		
	}
	
	/**
	 * Null should be changed to default value.
	 */
	@Test
	public void testNull() {
		final SetterOption opt = 
			new SetterOption(this, m2, converter, "DEFAULT", 'x', 
					Arity.OPTIONAL_ARGUMENT);
    expected = "DEFAULT";
		opt.setValue(null);
		assertTrue("Method was not invoked", methodCalled);
	}
}
