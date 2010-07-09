package ie.ucd.semantic_properties_plugin.file_checker;

import java.io.File;

import junit.framework.TestCase;

public class ConcurrencyTest extends TestCase{

	
	public void  testConProp(){
		
		/**Create Property.
		 * 
		 */
		File conPropFile= new File("resources/examples/concurrency.yaml");
		
		Property concurrencyProperty=new Property(conPropFile);
		
		/**Create sample  input String.
		 * 
		 */
		String sampleInput="concurrency CONCURRENT This class is fully thread-safe.";
		
		/**Create PropertyMatch for the property and string.
		 * 
		 */
		
		PropertyMatch match = new PropertyMatch(sampleInput,concurrencyProperty);
		
		assertTrue(match.isValid());
		
		
		File refPropFile=new File("resources/examples/concurrency_refinement.yaml");
		
		RefinementProperty refProp= new RefinementProperty(refPropFile);
		
//
//		
//		PropertyMatch refinedMatch=refProp.refine(match);
//		
//		assertTrue(refProp.isValidRefinement(refinedMatch,match));
		
		
		
		
	}
}
