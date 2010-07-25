package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.api.LevelId;
import ie.ucd.semanticproperties.plugin.api.ScopeId;
import ie.ucd.semanticproperties.plugin.customobjects.MyClass;
import ie.ucd.semanticproperties.plugin.customobjects.MyDate;
import ie.ucd.semanticproperties.plugin.customobjects.MyDescription;
import ie.ucd.semanticproperties.plugin.customobjects.MyEmail;
import ie.ucd.semanticproperties.plugin.customobjects.MyExpression;
import ie.ucd.semanticproperties.plugin.customobjects.MyFloat;
import ie.ucd.semanticproperties.plugin.customobjects.MyInt;
import ie.ucd.semanticproperties.plugin.customobjects.MyObject;
import ie.ucd.semanticproperties.plugin.customobjects.MyString;
import ie.ucd.semanticproperties.plugin.customobjects.MyThrowable;
import ie.ucd.semanticproperties.plugin.customobjects.MyURL;
import ie.ucd.semanticproperties.plugin.customobjects.MyVersion;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertySpecificationException;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Date;
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
  public void testConstructor() throws IOException, InvalidSemanticPropertySpecificationException {

    /**
     * Create SemanticPropertyLevelSpecification
     */
    SemanticPropertyLevelSpecification lr1 = new SemanticPropertyLevelSpecification(new File("resources/examples/junit/LReg1.yaml"));
    
    /**
     * Compare Level & Name. 
     */
    assertEquals(lr1.getLevel(), LevelId.JAVA_JML);
    assertEquals(lr1.getName(), "LReg1");
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
   * @throws IOException 
   * @throws InvalidSemanticPropertySpecificationException 
   */
  public void testTypes() throws InvalidSemanticPropertySpecificationException, IOException {
    SemanticPropertyLevelSpecification lr1 = new SemanticPropertyLevelSpecification(new File("resources/examples/junit/AllTypes.yaml"));
    
    /**
     * get gorups of objects and assert that they are what we expect.
     */
    LinkedHashMap<String, MyObject> objs = lr1.getReg().getGroupObj();
    
//    assertEquals(objs.get("c"), new MyClass("c",new Class("jav.lang.class")));

//    assertEquals(objs.get("d"), new MyDate("d",new Date(01/08/1988)));
    
    assertEquals(objs.get("e"), new MyDescription("e","a description"));
    
//    assertEquals(objs.get("f"), new MyEmail("f","mail@gmail.com"));
    
    assertEquals(objs.get("g"), new MyExpression("g","an expression"));
    
    assertEquals(objs.get("h"), new MyFloat("h",(float) 1.0009));
    
    assertEquals(objs.get("i"), new MyInt("i",24));
    
    assertEquals(objs.get("j"), new MyString("j","a string"));
    
//    assertEquals(objs.get("k"), new MyThrowable("k",new Throwable("java.lang.throwable")));
    
//    assertEquals(objs.get("l"), new MyURL("l",new URL("http://aurl.com")));
    
    assertEquals(objs.get("m"), new MyVersion("m",(float)1.0));
  }

}
