package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.api.LevelId;
import ie.ucd.semanticproperties.plugin.api.SemanticPropertiesHandler;
import ie.ucd.semanticproperties.plugin.api.SemanticPropertyInstance;

import java.io.File;

import junit.framework.TestCase;

public class ConcurrencyTest extends TestCase{

  /**Test Case for concurrency example.
   * 
   */

  public final void  testNewConProp() throws Exception {

    String bonInput = 
      "concurrency CONCURRENT 'This class is fully thread-safe.'";

    String javaInput = 
      "concurrency PARALLEL 'This class is fully thread-safe.  Moreover, we avoid any mention of locks.'";

    File conYaml = new File("resources/examples/concurrency_full.yaml");

    try {
      SemanticPropertiesHandler testHandler = new SemanticPropertiesHandler();
      testHandler.add(conYaml);
      SemanticPropertyInstance java = testHandler.parse(javaInput, "concurrency", LevelId.JAVA_JML);
      SemanticPropertyInstance bon = testHandler.parse(bonInput,  "concurrency", LevelId.BON_FORMAL);
      assertTrue(testHandler.isValidRefinement(bon, java));
      
      SemanticPropertyInstance refinedInstance = testHandler.generate(bon, LevelId.JAVA_JML);
      
//      assertTrue(testHandler.isValidRefinement(bon,refinedInstance));
    } catch (Exception e) {
      System.out.println("exceptional circumstances: " +e );
      throw e;
      //System.out.println(e.getMessage() );
    }
  }
}
