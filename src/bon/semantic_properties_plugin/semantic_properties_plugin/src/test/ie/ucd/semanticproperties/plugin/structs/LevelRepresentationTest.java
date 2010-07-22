package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertySpecificationException;

import java.io.File;
import java.io.IOException;

import junit.framework.TestCase;

/**
 * Test the important LevelRepresentation methods.
 * @author eo
 *
 */
public class LevelRepresentationTest extends TestCase {
  /**
   * Test the Constructor.
   * @throws InvalidSemanticPropertySpecificationException 
   * @throws IOException
   */
  public void testConstructor() throws IOException, InvalidSemanticPropertySpecificationException{
   
    LevelRepresenation lr1 = new LevelRepresenation(new File("resources/examples/junit/LReg1.yaml"));
    
    assertEquals(lr1.getLevel(), 5);
    assertEquals(lr1.getName(), "LReg1");
    
    
  }
  
  /**
   * Method that tests that all types are parsed correctly
   */
  public void testTypes(){
    
  }

}
