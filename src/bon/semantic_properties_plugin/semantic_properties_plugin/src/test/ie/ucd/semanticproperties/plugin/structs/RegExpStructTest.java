package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.customobjects.MyInt;
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
  public final void testConcatSimple() {

    LinkedHashMap < String, int[]> intMap = new LinkedHashMap < String, int []> ();
    LinkedHashMap < String, MyObject > obMap = new LinkedHashMap < String, MyObject > ();
    
    
    RegExpStruct eg1 = new RegExpStruct("(an exp)", intMap, obMap, 1);
    RegExpStruct eg2 = new RegExpStruct("(add on)", intMap, obMap, 1);

    RegExpStruct concat  = eg1.concat(eg2, "(", ")", 1);


    assertEquals(concat.getNumberOfGroups(), 3);
    assertEquals(concat.getExp(), "((an exp)(add on))");
  }

  /**
   * Test the concat() method.
   */
  public final void testConcatWithNonEmptyMaps() {

    LinkedHashMap < String, int[] > intMap1 = new LinkedHashMap < String, int []> ();
    int[] i = new int[1];
    i[0] = 5;
    intMap1.put("a", i);
    LinkedHashMap < String, MyObject > obMap1 = new LinkedHashMap < String, MyObject > ();
    obMap1.put("a", new MyInt("a",5));
    RegExpStruct eg1 = new RegExpStruct("(an exp)", intMap1, obMap1, 1);
    
    
    LinkedHashMap < String, int[] > intMap2 = new LinkedHashMap < String, int []> ();
    int[] i2 = new int[1];
    i2[0] = 5;
    intMap2.put("a", i2);
    LinkedHashMap < String, MyObject > obMap2 = new LinkedHashMap < String, MyObject > ();
    obMap2.put("b", new MyInt("b",6));
    RegExpStruct eg2 = new RegExpStruct("(more)", intMap2, obMap2, 1);

    RegExpStruct concat  = eg1.concat(eg2, "", "", 0);

    LinkedHashMap< String, MyObject> obMap1and2 = new LinkedHashMap< String, MyObject> ();
    obMap1and2.put("a", new MyInt("a",5));
    obMap1and2.put("b", new MyInt("b",6));
    
    assertEquals(concat.getNumberOfGroups(), 2);
    assertEquals(concat.getExp(), "(an exp)(more)");
    assertEquals(concat.getGroupObj(),obMap1and2);
  }

  
  
  /**
   * Test the overriden testEquals method.
   */
  public final void testEqualsSimple() {

    LinkedHashMap < String, int[] > intMap = new LinkedHashMap < String, int []> ();
    LinkedHashMap < String, MyObject > obMap = new LinkedHashMap < String, MyObject > ();
    String exp = "anexp";
    int num = 1;
    
    RegExpStruct eg1 = new RegExpStruct(exp, intMap, obMap, num);
    RegExpStruct eg2 = new RegExpStruct(exp, intMap, obMap, num);


    assertEquals(eg1,eg2);
  }
  
  
  /**
   * Test the overriden testEquals method.
   */
  public final void testEqualsWithNonEmptyMaps() {

    LinkedHashMap < String, int[] > intMap = new LinkedHashMap < String, int []> ();
    int[] i2 = new int[1];
    i2[0] = 2;
    intMap.put("hi", i2);
    LinkedHashMap < String, int []> intMap2 = new LinkedHashMap < String, int []> ();
    int[] i = new int[1];
    i[0] = 2;
    intMap2.put("hi", i);
    
    LinkedHashMap < String, MyObject > obMap = new LinkedHashMap < String, MyObject > ();
    LinkedHashMap < String, MyObject > obMap2 = new LinkedHashMap < String, MyObject > ();
    String exp = "anexp";
    int num = 1;
    
    RegExpStruct eg1 = new RegExpStruct(exp, intMap, obMap, num);
    RegExpStruct eg2 = new RegExpStruct(exp, intMap2, obMap2, num);


    assertEquals(eg1,eg2);
  }
  

}
