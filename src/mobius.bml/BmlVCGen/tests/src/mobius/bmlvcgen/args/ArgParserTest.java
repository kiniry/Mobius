package mobius.bmlvcgen.args;

import static org.junit.Assert.assertArrayEquals;
import mobius.bmlvcgen.args.Option.Arity;
import mobius.bmlvcgen.args.exceptions.ArgMissingException;
import mobius.bmlvcgen.args.exceptions.IllegalValueException;
import mobius.bmlvcgen.args.exceptions.UnknownOptionException;
import mobius.bmlvcgen.args.exceptions.ValueMissingException;

import org.junit.Before;
import org.junit.Test;

/**
 * Tests of argument parser.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 *
 */
public class ArgParserTest {
	private ArgParser parser;
	
	/**
	 * Initialization.
	 */
	@Before
	public void setUp() {
		parser = new ArgParser();
	}
	
	/**
	 * Test empty parser behavior 
	 * on empty argument list. 
	 */
	@Test
	public void testEmpty() throws Exception {
		final String[] other = parser.parse();
		assertArrayEquals("Invalid array returned", 
				new String[0], other);
	}
	
	/**
	 * Single, unrecognized short option as
	 * argument list.
	 */
	@Test(expected=UnknownOptionException.class)
	public void testUnrecognizedShort() throws Exception {
		parser.parse("-x");
	}
	
	/**
	 * Single, unrecognized long option as
	 * argument list.
	 */
	@Test(expected=UnknownOptionException.class)
	public void testUnrecognizedLong() throws Exception {
		parser.parse("--test");
	}
	
	/**
	 * Argument list contains only non-option arguments.
	 */
	@Test
	public void testNoOptions() throws Exception {
		final String[] other = 
			parser.parse("this", "is", "a", "test");
		assertArrayEquals("Non-option arguments changed", 
				new String[] { "this", "is", "a", "test" },
				other);
	}
	
	/**
	 * Single hyphen is not an option.
	 */
	@Test
	public void testSingleHyphen() throws Exception {
		final String[] other = parser.parse("-");
		assertArrayEquals("Invalid array returned", 
				new String[] {"-"}, other);
	}
	
	/**
	 * Argument list starting with '--'.
	 */
	@Test
	public void testOptionEnd() throws Exception {
		final String[] other = parser.parse("--", "-x", "--test");
		assertArrayEquals("Invalid array returned", 
				new String[] {"-x", "--test"}, other);		
	}
	
	/**
	 * Single, recognized short option without arguments.
	 */
	@Test
	public void testShortFlag() throws Exception {
		final MockOption opt = 
			new MockOption('c', Arity.NO_ARGUMENT);
		opt.expect((String)null);
		parser.addOption(opt);
		final String[] other = parser.parse("-c");
		assertArrayEquals("Invalid array returned",
				new String[0], other);
	}
	
	/**
	 * Single, recognized short option with 
	 * required argument.
	 */
	@Test
	public void testShortOption() throws Exception {
		final MockOption opt = 
			new MockOption('c', Arity.REQUIRED_ARGUMENT);
		opt.expect("value");
		parser.addOption(opt);
		final String[] other = parser.parse("-c", "value");
		assertArrayEquals("Invalid array returned",
				new String[0], other);
	}
	
	/**
	 * Single, recognized short option with 
	 * required argument not separated by whitespace.
	 */
	@Test
	public void testShortOptionWithoutSpace() throws Exception {
		final MockOption opt = 
			new MockOption('c', Arity.REQUIRED_ARGUMENT);
		opt.expect("value");
		parser.addOption(opt);
		final String[] other = parser.parse("-cvalue");
		assertArrayEquals("Invalid array returned",
				new String[0], other);
	}
	
	/**
	 * Short option with optional argument present.
	 */
	@Test
	public void testShortOptionalArgument() throws Exception {
		final MockOption opt = 
			new MockOption('c', Arity.OPTIONAL_ARGUMENT);
		opt.expect("value");
		parser.addOption(opt);
		final String[] other = parser.parse("-c", "value");
		assertArrayEquals("Invalid array returned",
				new String[0], other);		
	}
	
	/**
	 * Short option with optional argument not present.
	 */
	@Test
	public void testShortNoOptionalArgument() throws Exception {
		final MockOption opt = 
			new MockOption('c', Arity.OPTIONAL_ARGUMENT);
		opt.expect((String)null);
		parser.addOption(opt);
		final String[] other = parser.parse("-c");
		assertArrayEquals("Invalid array returned",
				new String[0], other);		
	}
	
	/**
	 * Three short options in one group.
	 */
	@Test
	public void testOptionGroup() throws Exception {
		final MockOption opt1 = 
			new MockOption('x', Arity.NO_ARGUMENT);
		final MockOption opt2 = 
			new MockOption('y', Arity.OPTIONAL_ARGUMENT);
		final MockOption opt3 = 
			new MockOption('z', Arity.NO_ARGUMENT);
		opt1.expect((String)null);
		opt2.expect((String)null);
		opt3.expect((String)null);
		parser.addOption(opt1);
		parser.addOption(opt2);
		parser.addOption(opt3);
		final String[] other = parser.parse("-xyz");
		assertArrayEquals("Invalid array returned",
				new String[0], other);		
	}
	
	/**
	 * Option group in which one option requires 
	 * an argument.
	 */
	@Test(expected=ValueMissingException.class)
	public void testInvalidOptionGroup() throws Exception {
		final MockOption opt1 = 
			new MockOption('x', Arity.NO_ARGUMENT);
		final MockOption opt2 = 
			new MockOption('y', Arity.REQUIRED_ARGUMENT);
		final MockOption opt3 = 
			new MockOption('z', Arity.NO_ARGUMENT);
		opt1.expect((String)null);
		opt2.expect((String)null);
		opt3.expect((String)null);
		parser.addOption(opt1);
		parser.addOption(opt2);
		parser.addOption(opt3);
		parser.parse("-xyz");
	}
	
	/**
	 * Required short option missing.
	 */
	@Test(expected=ArgMissingException.class) 
	public void testMissingArg() throws Exception {
		final MockOption opt = 
			new MockOption('c', Arity.NO_ARGUMENT);
		opt.expect();
		parser.addRequiredOption(opt);
		parser.parse();		
	}
	
	/**
	 * Required short option present.
	 */
	@Test 
	public void testRequiredShortOpt() throws Exception {
		final MockOption opt = 
			new MockOption('c', Arity.NO_ARGUMENT);
		opt.expect((String)null);
		parser.addRequiredOption(opt);
		final String[] other = parser.parse("-c");
		assertArrayEquals("Invalid array returned",
				new String[0], other);	
	}

	/**
	 * Single long option without argument.
	 */
	@Test 
	public void testLongOption() throws Exception {
		final MockOption opt = 
			new MockOption("test", Arity.NO_ARGUMENT);
		opt.expect((String)null);
		parser.addOption(opt);
		final String[] other = parser.parse("--test");
		assertArrayEquals("Invalid array returned",
				new String[0], other);	
	}
	
	/**
	 * Required long option present.
	 */
	@Test 
	public void testRequiredLongOpt() throws Exception {
		final MockOption opt = 
			new MockOption("test", Arity.NO_ARGUMENT);
		opt.expect((String)null);
		parser.addRequiredOption(opt);
		final String[] other = parser.parse("--test");
		assertArrayEquals("Invalid array returned",
				new String[0], other);	
	}
	
	/**
	 * Long option with optional argument present.
	 */
	@Test
	public void testLongOptionalArgument() throws Exception {
		final MockOption opt = 
			new MockOption("test", Arity.OPTIONAL_ARGUMENT);
		opt.expect("value");
		parser.addOption(opt);
		final String[] other = parser.parse("--test", "value");
		assertArrayEquals("Invalid array returned",
				new String[0], other);		
	}

	/**
	 * Long option with optional argument passed using '='.
	 */
	@Test
	public void testLongOptionalArgumentEq() throws Exception {
		final MockOption opt = 
			new MockOption("test", Arity.OPTIONAL_ARGUMENT);
		opt.expect("value");
		parser.addOption(opt);
		final String[] other = parser.parse("--test=value");
		assertArrayEquals("Invalid array returned",
				new String[0], other);		
	}
	
	/**
	 * Long option with optional argument missing.
	 */
	@Test
	public void testLongNoOptionalArgument() throws Exception {
		final MockOption opt1 = 
			new MockOption("test", Arity.OPTIONAL_ARGUMENT);
		final MockOption opt2 = 
			new MockOption('c', Arity.NO_ARGUMENT);
		opt1.expect((String)null);
		opt2.expect((String)null);
		parser.addOption(opt1);
		parser.addOption(opt2);
		final String[] other = parser.parse("--test", "-c");
		assertArrayEquals("Invalid array returned",
				new String[0], other);		
	}
	
	/**
	 * Long option with unexpected argument passed using '='.
	 */
	@Test(expected=IllegalValueException.class)
	public void testUnexpectedArgument() throws Exception {
		final MockOption opt = 
			new MockOption("test", Arity.NO_ARGUMENT);
		opt.expect();
		parser.addOption(opt);
		parser.parse("--test=value");	
	}
	
	/**
	 * Short option required argument starting with a hyphen.
	 */
	@Test
	public void testArgWithHyphen() throws Exception {
		final MockOption opt = 
			new MockOption('c', Arity.REQUIRED_ARGUMENT);
		opt.expect("-value");
		parser.addOption(opt);
		final String[] other = parser.parse("-c", "-value");
		assertArrayEquals("Invalid array returned",
				new String[0], other);
	}
	
	/**
	 * Short option with optional argument should
	 * not capture values starting with a hyphen.
	 */
	@Test
	public void testOptionalArgWithHyphen() throws Exception {
		final MockOption opt = 
			new MockOption('c', Arity.OPTIONAL_ARGUMENT);
		opt.expect(null, null);
		parser.addOption(opt);
		final String[] other = parser.parse("-c", "-c");
		assertArrayEquals("Invalid array returned",
				new String[0], other);
	}
	
	/**
	 * Non-option arguments not at the end of argument list.
	 */
	@Test
	public void testNonOptionArgs() throws Exception {
		final MockOption opt1 = 
			new MockOption('x', Arity.NO_ARGUMENT);
		final MockOption opt2 = 
			new MockOption('y', Arity.REQUIRED_ARGUMENT);
		final MockOption opt3 = 
			new MockOption('z', Arity.NO_ARGUMENT);
		opt1.expect((String)null);
		opt2.expect("yvalue");
		opt3.expect((String)null);
		parser.addOption(opt1);
		parser.addOption(opt2);
		parser.addOption(opt3);
		final String[] other = 
			parser.parse("-x", "first", "-y", "yvalue", 
					"second", "-z", "third");
		assertArrayEquals("Invalid array returned",
				new String[] {"first", "second", "third"},
				other);				
	}
	
  /**
   * Bug - non-option arguments right after long option
   * with parameter are not recognized.
   */
  @Test
  public void testBug1() throws Exception {
    final MockOption opt1 = 
      new MockOption("test", Arity.REQUIRED_ARGUMENT);
    opt1.expect("value");
    parser.addOption(opt1);
    final String[] other = 
      parser.parse("--test=value", "arg");
    assertArrayEquals("Invalid array returned",
        new String[] {"arg"},
        other);       
  }
}
