
package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.structs.LevelRepresenation;
import ie.ucd.semanticproperties.plugin.structs.Refinement;

import java.io.File;

import junit.framework.TestCase;


/**
 * @author eo
 *
 */
public class RefinementTest extends TestCase {

  /**
   * Check refinement prefix
   */
  public final void testPrefixRefinement() {

    try {

      String refinementPropertyString = "";
      Refinement refinement =  new Refinement(refinementPropertyString);

      String sourcePropertyString = "";
      LevelRepresenation sourceProperty = new LevelRepresenation(sourcePropertyString);

      String refinedPropertyString = "";
      LevelRepresenation refinedProperty = new LevelRepresenation(refinedPropertyString);
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
