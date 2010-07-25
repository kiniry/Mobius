package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.api.LevelId;
import ie.ucd.semanticproperties.plugin.api.ScopeId;
import ie.ucd.semanticproperties.plugin.customobjects.MyObject;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertySpecificationException;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedHashMap;

import junit.framework.TestCase;

/**
 * Test the important LevelRepresentation methods.
 * @author eo
 *
 */
public class SemanticPropertyLevelSpecificationTest extends TestCase {
  /**
   * Test the Constructor.
   * @throws InvalidSemanticPropertySpecificationException 
   * @throws IOException
   */
  public void testConstructor() throws IOException, InvalidSemanticPropertySpecificationException{
   
    SemanticPropertyLevelSpecification lr1 = new SemanticPropertyLevelSpecification(new File("resources/examples/junit/LReg1.yaml"));
    
    assertEquals(lr1.getLevel(), LevelId.JAVA_JML);
    assertEquals(lr1.getName(), "LReg1");
    assertEquals(lr1.getLevel(), LevelId.JAVA_JML);
    /**
     * compare Scope.
     */
    ArrayList<ScopeId> scopeList = new ArrayList<ScopeId>();
    scopeList.add(ScopeId.MODULE);
    scopeList.add(ScopeId.FEATURE);
    assertEquals(lr1.getScope(), scopeList);
    /**
     * Compare Description
     */
    assertEquals(lr1.getDescription(), "Describes LR eg 1.");
    /**
     * Compare regular expression.
     */
    LinkedHashMap < String , Integer> capGroup= new LinkedHashMap< String , Integer>();
    capGroup.put("choice1", 1);
    RegExpStruct li = new RegExpStruct("LReg1[\\s+](a|b)(?:[\\s+]c)?",capGroup, new LinkedHashMap<String, MyObject >(),1);
    assertEquals(lr1.getReg(),li);
  }
  
  /**
   * Method that tests that all types are parsed correctly
   */
  public void testTypes(){
    
  }

}
