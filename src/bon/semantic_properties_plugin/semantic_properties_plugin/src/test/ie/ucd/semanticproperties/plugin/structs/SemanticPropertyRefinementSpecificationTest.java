
package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.api.LevelId;
import ie.ucd.semanticproperties.plugin.api.ScopeId;
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
import java.util.ArrayList;

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
   *
   */
  public final void testPrefixRefinement() throws SemanticPropertyException , IOException {
    SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
    testProp.add(new File("resources/examples/junit/prefixEg.yaml"));
    SemanticPropertyInstance instance1 = testProp.parse("prefixEg a short des. (an expr) 'a string'", LevelId.BON_FORMAL,ScopeId.MODULE);
    SemanticPropertyInstance instance2 = testProp.parse("prefixEg abba short description. (an expression) 'a string plus some'", LevelId.JAVA_JML,ScopeId.MODULE);
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
    SemanticPropertyInstance instance1 = testProp.parse("suffixEg short des. (an expr) ' string'", LevelId.BON_FORMAL,ScopeId.MODULE);
    SemanticPropertyInstance instance2 = testProp.parse("suffixEg  a short des. (yet another an expr) 'not another string'",LevelId.JAVA_JML,ScopeId.MODULE);
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
  public final void testEqualsRefinement1() throws SemanticPropertyException, IOException{
    SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
    testProp.add(new File("resources/examples/junit/equalsEg.yaml"));
    SemanticPropertyInstance instance1 = testProp.parse("equalsEg short des. (an expr) ' string'", LevelId.BON_FORMAL,ScopeId.MODULE);
    SemanticPropertyInstance instance2 = testProp.parse("equalsEg short des. (an expr) ' string'", LevelId.JAVA_JML,ScopeId.MODULE);
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
  public final void testEqualsRefinement2() throws SemanticPropertyException, IOException{
    SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
    testProp.add(new File("resources/examples/junit/equalsEg2.yaml"));
    SemanticPropertyInstance instance1 = testProp.parse("equalsEg java.lang.t class.c g@gmail.com 27-08-1988 0.1 http://anurl.com", LevelId.BON_FORMAL,ScopeId.MODULE);
    SemanticPropertyInstance instance2 = testProp.parse("equalsEg java.lang.t class.c g@gmail.com 27-08-1988 0.1 http://anurl.com", LevelId.JAVA_JML,ScopeId.MODULE);
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
    SemanticPropertyInstance instance1 = testProp.parse("substringEg smallstring. (an expr) 's'",LevelId.BON_FORMAL,ScopeId.MODULE);
    SemanticPropertyInstance instance2 = testProp.parse("substringEg a smallstring of. (also an expr dont ya know) ' string'", LevelId.JAVA_JML,ScopeId.MODULE);
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
    SemanticPropertyInstance instance1 = testProp.parse("lessthanEg 3.0 5 5", LevelId.BON_FORMAL,ScopeId.MODULE);
    SemanticPropertyInstance instance2 = testProp.parse("lessthanEg 22.5 6 6", LevelId.JAVA_JML,ScopeId.MODULE);
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
    SemanticPropertyInstance instance1 = testProp.parse("lessthanorequalsEg 3.0 3 -5", LevelId.BON_FORMAL,ScopeId.MODULE);
    SemanticPropertyInstance instance2 = testProp.parse("lessthanorequalsEg 3.0 4 -1", LevelId.JAVA_JML,ScopeId.MODULE);
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
  SemanticPropertyInstance instance1 = testProp.parse("greaterthanEg 30.0 15 25",LevelId.BON_FORMAL,ScopeId.MODULE);
  SemanticPropertyInstance instance2 = testProp.parse("greaterthanEg 4.5 6 15", LevelId.JAVA_JML,ScopeId.MODULE);
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
  SemanticPropertyInstance instance1 = testProp.parse("greaterthanorequalsEg 5.0 16 16", LevelId.BON_FORMAL,ScopeId.MODULE);
  SemanticPropertyInstance instance2 = testProp.parse("greaterthanorequalsEg 4.5 6 15", LevelId.JAVA_JML,ScopeId.MODULE);
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
  SemanticPropertyInstance instance1 = testProp.parse("equalsnumEg 3.0 5 5", LevelId.BON_FORMAL,ScopeId.MODULE);
  SemanticPropertyInstance instance2 = testProp.parse("equalsnumEg 3.0 5 5",LevelId.JAVA_JML,ScopeId.MODULE);
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
