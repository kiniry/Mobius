package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.customobjects.MyObject;

import java.util.LinkedHashMap;

import junit.framework.TestCase;

/**
 * Test all the methods of RegExpStruct.
 * @author eo
 *
 */
public class RegExpStructTest extends TestCase {
  /**
   * Test the concat() method.
   */
  public final void testConcat() {

    LinkedHashMap < String, Integer > intMap = new LinkedHashMap < String, Integer > ();
    LinkedHashMap < String, MyObject > obMap = new LinkedHashMap < String, MyObject > ();
    RegExpStruct eg1 = new RegExpStruct("(an exp)", intMap, obMap, 1);
    RegExpStruct eg2 = new RegExpStruct("(add on)", intMap, obMap, 1);

    RegExpStruct concat  = eg1.concat(eg2, "(", ")", 1);


    assertEquals(concat.getNumberOfGroups(), 3);
    assertEquals(concat.getExp(), "((an exp)(add on))");
  }

  
  /**
   * Test the overriden testEquals method.
   */
  public final void testEqualsSimple() {

    LinkedHashMap < String, Integer > intMap = new LinkedHashMap < String, Integer > ();
    LinkedHashMap < String, MyObject > obMap = new LinkedHashMap < String, MyObject > ();
    String exp = "anexp";
    Integer num = 1;
    
    RegExpStruct eg1 = new RegExpStruct(exp, intMap, obMap, num);
    RegExpStruct eg2 = new RegExpStruct(exp, intMap, obMap, num);


    assertEquals(eg1,eg2);
  }
  
  
  /**
   * Test the overriden testEquals method.
   */
  public final void testEqualsWithFullMap() {

    LinkedHashMap < String, Integer > intMap = new LinkedHashMap < String, Integer > ();
    intMap.put("hi", 2);
    LinkedHashMap < String, Integer > intMap2 = new LinkedHashMap < String, Integer > ();
    intMap2.put("hi", 2);
    
    LinkedHashMap < String, MyObject > obMap = new LinkedHashMap < String, MyObject > ();
    LinkedHashMap < String, MyObject > obMap2 = new LinkedHashMap < String, MyObject > ();
    String exp = "anexp";
    Integer num = 1;
    
    RegExpStruct eg1 = new RegExpStruct(exp, intMap, obMap, num);
    RegExpStruct eg2 = new RegExpStruct(exp, intMap2, obMap2, num);


    assertEquals(eg1,eg2);
  }
  

}
