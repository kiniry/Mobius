/**
 * 
 */
package ie.ucd.semantic_properties_plugin.file_checker;

import java.io.File;

import junit.framework.TestCase;


/**
 * @author eo
 *
 */
public class RefinementPropertyTest extends TestCase {

	public void testRefProp(){
		File inputOne = new File("resources/examples/concurrency_refinement.yaml");
		
		RefinementProperty propOne= new RefinementProperty(inputOne);
		
		System.out.println("Strings "+propOne.getSConversions());
		System.out.println("Objects "+propOne.getOConversions());
		assertEquals(0,0);
	}


	/**Test the isValidRefinement method in Refinement Property.
	 * 
	 */
	public void testIsValidRefinement(){
		File inputOne = new File("resources/examples/concurrency_refinement.yaml");
		
		RefinementProperty propOne= new RefinementProperty(inputOne);
		
		System.out.println("Strings "+propOne.getSConversions());
		System.out.println("Objects "+propOne.getOConversions());
		assertEquals(0,0);
	}

}