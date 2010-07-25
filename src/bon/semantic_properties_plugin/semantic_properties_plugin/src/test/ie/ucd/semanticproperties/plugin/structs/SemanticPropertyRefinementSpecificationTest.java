
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
   * Check refinement prefix
   * @throws IOException 
   * @throws IOException 
   * @throws InvalidSemanticPropertySpecificationException 
   * @throws FileNotFoundException 
   * @throws SemanticPropertyNotValidAtScopeException 
   * @throws InvalidSemanticPropertyUseException 
   * @throws UnknownPropertyException 
   * @throws UnknownVariableIdentifierException 
   * @throws IncompatibleSemanticPropertyInstancesException 
   */
  public final void testPrefixRefinement() throws SemanticPropertyException, IOException {
    
    SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
    testProp.add(new File("resources/examples/junit/prefixEg.yaml"));
    SemanticPropertyInstance instance1 = testProp.parse("prefixEg a short des. (an expr) 'a string'","prefixEg", LevelId.BON_FORMAL);
    SemanticPropertyInstance instance2 = testProp.parse("prefixEg abba short description. (an expression) 'a string plus some'","prefixEg", LevelId.JAVA_JML);
    assertTrue(testProp.isValidRefinement(instance1, instance2));
  }
  /**
   * Check suffix refinement.
   * @throws SemanticPropertyNotValidAtScopeException 
   * @throws InvalidSemanticPropertyUseException 
   * @throws UnknownPropertyException 
   * @throws IOException 
   * @throws InvalidSemanticPropertySpecificationException 
   */
  public final void testSuffixRefinement() throws SemanticPropertyException, IOException{
    SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
    testProp.add(new File("resources/examples/junit/suffixEg.yaml"));
    SemanticPropertyInstance instance1 = testProp.parse("suffixEg short des. (an expr) ' string'","suffixEg", LevelId.BON_FORMAL);
    SemanticPropertyInstance instance2 = testProp.parse("suffixEg  a short des. (yet another an expr) 'not another string'","suffixEg", LevelId.JAVA_JML);
    assertTrue(testProp.isValidRefinement(instance1, instance2));
    
  }
  /**
   * Check equals refinement.
   * @throws SemanticPropertyNotValidAtScopeException 
   * @throws InvalidSemanticPropertyUseException 
   * @throws UnknownPropertyException 
   * @throws IOException 
   * @throws InvalidSemanticPropertySpecificationException 
   */
  public final void testEqualsRefinement() throws SemanticPropertyException, IOException{
    SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
    testProp.add(new File("resources/examples/junit/equalsEg.yaml"));
    SemanticPropertyInstance instance1 = testProp.parse("equalsEg short des. (an expr) ' string'","equalsEg", LevelId.BON_FORMAL);
    SemanticPropertyInstance instance2 = testProp.parse("equalsEg short des. (an expr) ' string'","equalsEg", LevelId.JAVA_JML);
    assertTrue(testProp.isValidRefinement(instance1, instance2));
    
  }
  /**
   * Check substring refinement.
   * @throws SemanticPropertyNotValidAtScopeException 
   * @throws InvalidSemanticPropertyUseException 
   * @throws UnknownPropertyException 
   * @throws IOException 
   * @throws InvalidSemanticPropertySpecificationException 
   */
  public final void testSubstringRefinement() throws SemanticPropertyException, IOException{
    SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
    testProp.add(new File("resources/examples/junit/substringEg.yaml"));
    SemanticPropertyInstance instance1 = testProp.parse("substringEg substring. (an expr) 's'","substringEg", LevelId.BON_FORMAL);
    SemanticPropertyInstance instance2 = testProp.parse("substringEg a substring of. (also an expr dont ya know) ' string'","substringEg", LevelId.JAVA_JML);
    assertTrue(testProp.isValidRefinement(instance1, instance2));
    
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
    SemanticPropertyInstance instance2 = testProp.parse("lessthanEg 2.5 4 -1","lessthanEg", LevelId.JAVA_JML);
    assertTrue(testProp.isValidRefinement(instance1, instance2));
    
  }

/**
 * Check lessthan refinement.
 * @throws SemanticPropertyException
 * @throws IOException 

 */
public final void testGreaterThanRefinement() throws SemanticPropertyException, IOException{
  SemanticPropertiesHandler testProp = new SemanticPropertiesHandler();
  testProp.add(new File("resources/examples/junit/greaterthanEg.yaml"));
  SemanticPropertyInstance instance1 = testProp.parse("greaterthanEg 3.0 5 5","greaterthanEg", LevelId.BON_FORMAL);
  SemanticPropertyInstance instance2 = testProp.parse("greaterthanEg 4.5 6 15","greaterthanEg", LevelId.JAVA_JML);
  assertTrue(testProp.isValidRefinement(instance1, instance2));
  
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
