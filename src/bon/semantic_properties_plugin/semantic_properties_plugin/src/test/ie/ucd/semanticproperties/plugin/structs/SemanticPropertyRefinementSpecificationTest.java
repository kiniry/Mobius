
package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.structs.SemanticPropertyLevelSpecification;
import ie.ucd.semanticproperties.plugin.structs.SemanticPropertyRefinementSpecification;

import java.io.File;

import junit.framework.TestCase;


/**
 * @author eo
 *
 */
public class SemanticPropertyRefinementSpecificationTest extends TestCase {

  /**
   * Check refinement prefix
   */
  public final void testPrefixRefinement() {

    try {

      String refinementPropertyString = "";
      SemanticPropertyRefinementSpecification semanticPropertyRefinementSpecification =  new SemanticPropertyRefinementSpecification(refinementPropertyString);

      String sourcePropertyString = "";
      SemanticPropertyLevelSpecification sourceProperty = new SemanticPropertyLevelSpecification(sourcePropertyString);

      String refinedPropertyString = "";
      SemanticPropertyLevelSpecification refinedProperty = new SemanticPropertyLevelSpecification(refinedPropertyString);
    } catch(Exception e) {

    }
    assertTrue(true);
  }
  /**
   * Check suffix refinement.
   */
  public final void textSuffixRefinement(){
    
  }
  /**
   * Check constructor
   */
  public final void testConstructor(){
    
  }
  /**
   * Check isValidRefinement method.
   */
  public final void tetIsValidRefinement(){
    
  }
  

}
