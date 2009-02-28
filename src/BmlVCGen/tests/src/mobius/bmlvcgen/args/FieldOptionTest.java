package mobius.bmlvcgen.args;

import static org.junit.Assert.assertEquals;

import java.lang.reflect.Field;

import mobius.bmlvcgen.args.Option.Arity;
import mobius.bmlvcgen.args.converters.Converter;
import mobius.bmlvcgen.args.converters.DefaultConverter;

import org.junit.Before;
import org.junit.Test;

/**
 * Tests for class FieldOption.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class FieldOptionTest {
	public String field;
	private Field f;
	private Converter converter;
	
	/** Initialization. */
	@Before
	public void setUp() throws Exception {
		field = "Old value.";
		f = this.getClass().getField("field");
		converter = new DefaultConverter();
	}
	
	/** Simple test. */
	@Test
	public void testSetter() {
		final FieldOption opt = 
			new FieldOption(this, f, converter, null, 'x', 
					Arity.REQUIRED_ARGUMENT);
		opt.setValue("New value.");
		assertEquals("Value not modified", 
				"New value.", field);
	}
	
	/** Null value should be changed to default value. */
	@Test
	public void testNull() {
		final FieldOption opt = 
			new FieldOption(this, f, converter, "Default value", 
					'x', Arity.OPTIONAL_ARGUMENT);
		opt.setValue(null);
		assertEquals("Default value not set", 
				"Default value", field);
	}	
}
