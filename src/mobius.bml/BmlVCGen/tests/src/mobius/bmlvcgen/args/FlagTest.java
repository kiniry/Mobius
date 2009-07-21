package mobius.bmlvcgen.args;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import mobius.bmlvcgen.args.Option.Arity;

import org.junit.Test;

/**
 * Test of Flag and FlagOption.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class FlagTest {
	
	/**
	 * Test if short options returned by getOption
	 * behave as they should.
	 */
	@Test
	public void testGetShortOption() throws Exception {
		final Flag f = new Flag(true);
		final Option o = f.getOption('x', false);
		assertNotNull("getOption returned null", o);
		assertEquals("Invalid option arity", 
				o.getArity(), Arity.NO_ARGUMENT);
		assertNotNull("Invalid (null) option short name", 
				o.getShortName());
		assertEquals("Invalid option short name", 
				o.getShortName().charValue(), 'x');
		assertNull("Invalid option long name", o.getLongName());
		o.setValue(null);
		assertFalse("Value not changed by the option", 
				f.getValue());
	}
	
	/**
	 * Test if long options returned by getOption
	 * behave as they should.
	 */
	@Test
	public void testGetLongOption() throws Exception {
		final Flag f = new Flag(true);
		final Option o = f.getOption("xyz", false);
		assertNotNull("getOption returned null", o);
		assertEquals("Invalid option arity", 
				o.getArity(), Arity.NO_ARGUMENT);
		assertEquals("Invalid option long name", 
				o.getLongName(), "xyz");
		assertNull("Invalid option short name", o.getShortName());
		o.setValue(null);
		assertFalse("Value not changed by the option", 
				f.getValue());
	}
	
	/**
	 * Test if options returned by getOption
	 * behave as they should.
	 */
	@Test
	public void testGetOption() throws Exception {
		final Flag f = new Flag(true);
		Option o = f.getOption('x', "xyz", false);
		assertNotNull(o);
		assertEquals("Invalid option arity", 
				o.getArity(), Arity.NO_ARGUMENT);
		assertEquals("Invalid option long name", 
				o.getLongName(), "xyz");
		assertNotNull("Invalid (null) option short name", 
				o.getShortName());
		assertEquals("Invalid option short name", 
				o.getShortName().charValue(), 'x');
		o.setValue(null);
		assertFalse("Value not changed by the option", 
				f.getValue());
	}	

}
