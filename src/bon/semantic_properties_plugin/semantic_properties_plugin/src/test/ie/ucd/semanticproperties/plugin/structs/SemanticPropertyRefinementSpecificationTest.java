
package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.api.LevelId;
import ie.ucd.semanticproperties.plugin.api.SemanticPropertiesHandler;
import ie.ucd.semanticproperties.plugin.api.SemanticPropertyInstance;
import ie.ucd.semanticproperties.plugin.exceptions.IncompatibleSemanticPropertyInstancesException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertySpecificationException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertyUseException;
import ie.ucd.semanticproperties.plugin.exceptions.SemanticPropertyException;
import ie.ucd.semanticproperties.plugin.exceptions.SemanticPropertyNotValidAtScopeException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownLevelException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownPropertyException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownScopeException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownVariableIdentifierException;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

import junit.framework.TestCase;


/**
 * @author eo
 *
 */
public class SemanticPropertyRefinementSpecificationTest extends TestCase {

  /**
   *Check refinement prefix.
   * @throws SemanticPropertyException
   * @throws IOException
   */
  public final void testPrefixRefinement() throws SemanticPropertyException , IOException {
    SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
    testProp.add(new File("resources/examples/junit/prefixEg.yaml"));
    SemanticPropertyInstance instance1 = testProp.parse("prefixEg a short des. (an expr) 'a string'","prefixEg", LevelId.BON_FORMAL);
    SemanticPropertyInstance instance2 = testProp.parse("prefixEg abba short description. (an expression) 'a string plus some'","prefixEg", LevelId.JAVA_JML);
    assertTrue(testProp.isValidRefinement(instance1, instance2));
    /**
     * Check that generate method works.
     */
    assertTrue(testProp.isValidRefinement(instance1, testProp.generate(instance1, LevelId.JAVA_JML)));
  }
  /**
   * Check suffix refinement.
   * @throws SemanticPropertyException
   * @throws IOException
   */
  public final void testSuffixRefinement() throws SemanticPropertyException, IOException{
    SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
    testProp.add(new File("resources/examples/junit/suffixEg.yaml"));
    SemanticPropertyInstance instance1 = testProp.parse("suffixEg short des. (an expr) ' string'","suffixEg", LevelId.BON_FORMAL);
    SemanticPropertyInstance instance2 = testProp.parse("suffixEg  a short des. (yet another an expr) 'not another string'","suffixEg", LevelId.JAVA_JML);
    assertTrue(testProp.isValidRefinement(instance1, instance2));
    /**
     * Check that generate method works.
     */
    assertTrue(testProp.isValidRefinement(instance1, testProp.generate(instance1, LevelId.JAVA_JML)));
  }
  /**
   * Check equals refinement.
   * @throws SemanticPropertyException
   * @throws IOException
   */
  public final void testEqualsRefinement() throws SemanticPropertyException, IOException{
    SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
    testProp.add(new File("resources/examples/junit/equalsEg.yaml"));
    SemanticPropertyInstance instance1 = testProp.parse("equalsEg short des. (an expr) ' string'","equalsEg", LevelId.BON_FORMAL);
    SemanticPropertyInstance instance2 = testProp.parse("equalsEg short des. (an expr) ' string'","equalsEg", LevelId.JAVA_JML);
    assertTrue(testProp.isValidRefinement(instance1, instance2));
    /**
     * Check that generate method works.
     */
    assertTrue(testProp.isValidRefinement(instance1, testProp.generate(instance1, LevelId.JAVA_JML)));
  }
  /**
   * Check substring refinement.
   * @throws SemanticPropertyException
   * @throws IOException
   */
  public final void testSubstringRefinement() throws SemanticPropertyException, IOException{
    SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
    testProp.add(new File("resources/examples/junit/substringEg.yaml"));
    SemanticPropertyInstance instance1 = testProp.parse("substringEg smallstring. (an expr) 's'","substringEg", LevelId.BON_FORMAL);
    SemanticPropertyInstance instance2 = testProp.parse("substringEg a smallstring of. (also an expr dont ya know) ' string'","substringEg", LevelId.JAVA_JML);
    assertTrue(testProp.isValidRefinement(instance1, instance2));
    /**
     * Check that generate method works.
     */
    assertTrue(testProp.isValidRefinement(instance1, testProp.generate(instance1, LevelId.JAVA_JML)));
  }
  /**
   * Check lessthan refinement.
   * @throws SemanticPropertyException
   * @throws IOException

   */
  public final void testLestThanRefinement() throws SemanticPropertyException, IOException{
    SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
    testProp.add(new File("resources/examples/junit/lessThanEg.yaml"));
    SemanticPropertyInstance instance1 = testProp.parse("lessthanEg 3.0 5 5","lessthanEg", LevelId.BON_FORMAL);
    SemanticPropertyInstance instance2 = testProp.parse("lessthanEg 22.5 6 6","lessthanEg", LevelId.JAVA_JML);
    assertTrue(testProp.isValidRefinement(instance1, instance2));
    /**
     * Check that generate method works.
     */
    assertTrue(testProp.isValidRefinement(instance1, testProp.generate(instance1, LevelId.JAVA_JML)));
  }
  /**
   * Check lessthanorequals refinement.
   * @throws SemanticPropertyException
   * @throws IOException
   */
  public final void testLestThanOrEqualsRefinement() throws SemanticPropertyException, IOException {
    SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
    testProp.add(new File("resources/examples/junit/lessthanorequalsEg.yaml"));
    SemanticPropertyInstance instance1 = testProp.parse("lessthanorequalsEg 3.0 3 -5","lessthanorequalsEg", LevelId.BON_FORMAL);
    SemanticPropertyInstance instance2 = testProp.parse("lessthanorequalsEg 3.0 4 -1","lessthanorequalsEg", LevelId.JAVA_JML);
    assertTrue(testProp.isValidRefinement(instance1, instance2));
    /**
     * Check that generate method works.
     */
    assertTrue(testProp.isValidRefinement(instance1, testProp.generate(instance1, LevelId.JAVA_JML)));
  }


/**
 * Check greaterthan refinement.
 * @throws SemanticPropertyException
 * @throws IOException 

 */
public final void testGreaterThanRefinement() throws SemanticPropertyException, IOException{
  SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
  testProp.add(new File("resources/examples/junit/greaterthanEg.yaml"));
  SemanticPropertyInstance instance1 = testProp.parse("greaterthanEg 30.0 15 25","greaterthanEg", LevelId.BON_FORMAL);
  SemanticPropertyInstance instance2 = testProp.parse("greaterthanEg 4.5 6 15","greaterthanEg", LevelId.JAVA_JML);
  assertTrue(testProp.isValidRefinement(instance1, instance2));
  /**
   * Check that generate method works.
   */
  assertTrue(testProp.isValidRefinement(instance1, testProp.generate(instance1, LevelId.JAVA_JML)));
  
}

/**
 * Check greaterthanorequals refinement.
 * @throws SemanticPropertyException
 * @throws IOException 

 */
public final void testGreaterThanOrEqualsRefinement() throws SemanticPropertyException, IOException{
  SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
  testProp.add(new File("resources/examples/junit/greaterthanorequalsEg.yaml"));
  SemanticPropertyInstance instance1 = testProp.parse("greaterthanorequalsEg 5.0 16 16","greaterthanorequalsEg", LevelId.BON_FORMAL);
  SemanticPropertyInstance instance2 = testProp.parse("greaterthanorequalsEg 4.5 6 15","greaterthanorequalsEg", LevelId.JAVA_JML);
  assertTrue(testProp.isValidRefinement(instance1, instance2));
  /**
   * Check that generate method works.
   */
  assertTrue(testProp.isValidRefinement(instance1, testProp.generate(instance1, LevelId.JAVA_JML)));
  
}

/**
 * Check equals for num refinement.
 * @throws SemanticPropertyException
 * @throws IOException 

 */
public final void testEqualsForNumRefinement() throws SemanticPropertyException, IOException{
  SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
  testProp.add(new File("resources/examples/junit/equalsnumEg.yaml"));
  SemanticPropertyInstance instance1 = testProp.parse("equalsnumEg 3.0 5 5","equalsnumEg", LevelId.BON_FORMAL);
  SemanticPropertyInstance instance2 = testProp.parse("equalsnumEg 3.0 5 5","equalsnumEg", LevelId.JAVA_JML);
  assertTrue(testProp.isValidRefinement(instance1, instance2));
  /**
   * Check that generate method works.
   */
  assertTrue(testProp.isValidRefinement(instance1, testProp.generate(instance1, LevelId.JAVA_JML)));
  
}
  /**
   * Check constructor
   */
  public final void testConstructor(){
    
  }
  /**
   * Check isValidRefinement method.
   */
  public final void testIsValidRefinement(){
    
  }
  

}
