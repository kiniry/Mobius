package ie.ucd.semantic_properties_plugin.file_checker;

import java.io.File;

import junit.framework.TestCase;

public class ConcurrencyTest extends TestCase{

	/**Test Case for concurrency example.
	 * 
	 */
	public final void  testConProp() {
		
		/**Create bon property and match.
		 * 
		 */
		File bonYaml = new File("resources/examples/concurrency_bon.yaml");
		Property conBonProp = new Property(bonYaml);
		String bonInput = 
			"concurrency CONCURRENT 'This class is fully thread-safe.'";
		PropertyMatch bonMatch = new PropertyMatch(bonInput, conBonProp);
		/**Check if its a valid match.
		 * 
		 */
		assertTrue(bonMatch.isValid());
		

		/**Create java property and match.
		 * 
		 */
		File javaYaml = new File("resources/examples/concurrency_java.yaml");
		Property conJavaProp = new Property(javaYaml);
		String javaInput = 
			"concurrency PARALLEL 'This class is fully thread-safe.  Moreover, we avoid any mention of locks.'";
		PropertyMatch javaMatch = new PropertyMatch(javaInput, conJavaProp);
		/**Check if its a valid match.
		 * 
		 */
		assertTrue(javaMatch.isValid());
		
		/**Create refinement Property, check isValidRefinement().
		 * <p>Create refinement Property and check 
		 * if bonMatch refines to javaMatch.</p>
		 */
		File refinementYaml = 
			new File("resources/examples/concurrency_refinement.yaml");
		
		RefinementProperty refProp =
			new RefinementProperty(refinementYaml);
		
		assertTrue(refProp.isValidRefinement(bonMatch, javaMatch));
//
//		
//		PropertyMatch refinedMatch=refProp.refine(match);
//		
//		assertTrue(refProp.isValidRefinement(refinedMatch,match));
		
		
		
		
	}
}
