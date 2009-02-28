package mobius.bmlvcgen.args.annot;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import mobius.bmlvcgen.args.ArgParser;

import org.junit.Test;

/**
 * Annotation reader tests.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class AnnotReaderTest {
	/**
	 * Annotated class.
	 */
	public static final class Options {
		/** Integer field. */
		@CmdParam(shortName='i')
		public int intField = 1;
		/** String field. */
		@CmdParam(shortName='s', 
				valueOptional=true, defaultValue="1")
		public String stringField = "0";
		/** Boolean field. */
		@CmdParam(shortName='b')
		public boolean boolField = false;
		
		/**
		 * Set value of the integer field.
		 * @param value New value.
		 */
		@CmdParam(longName="int")
		public void setIntField(final int value) {
			intField = value;
		}
		
		/**
		 * Set value of the string field.
		 * @param value New value.
		 */	
		@CmdParam(longName="string", 
				valueOptional=true, defaultValue="1")
		public void setStringField(final String value) {
			stringField = value;
		}
		
		/**
		 * Set value of the boolean field to true.
		 */
		@CmdParam(longName="bool")
		public void setBoolFieldToTrue() {
			boolField = true;
		}
	}
	
	/**
	 * Test options backed by fields.
	 */
	@Test
	public void testFieldOptions() throws Exception {
		final Options opts = new Options();
		final ArgParser parser = new ArgParser();
		AnnotReader.findOptions(opts, parser);
		parser.parse("-i", "42", "-s", "-b", "ignored");
		assertEquals("Integer field value is invalid", 
				42, opts.intField);
		assertEquals("String field value is invalid", 
				"1", opts.stringField);
		assertTrue("Boolean field value is invalid", 
				opts.boolField);
	}
	
	/**
	 * Test options backed by methods.
	 */
	@Test
	public void testMethodOptions() throws Exception {
		final Options opts = new Options();
		final ArgParser parser = new ArgParser();
		AnnotReader.findOptions(opts, parser);
		parser.parse("--int", "42", "--string", "--bool");
		assertEquals("Integer field value is invalid", 
				42, opts.intField);
		assertEquals("String field value is invalid", 
				"1", opts.stringField);
		assertTrue("Boolean field value is invalid", 
				opts.boolField);
	}
}
