package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.customobjects.MyDescription;
import ie.ucd.semanticproperties.plugin.customobjects.MyExpression;
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
  
  
  public final String space = "[\\s]+";
  public final String opSpace = "[\\s]*";

  /**
   * Test object constructor.
   */
  public final void testConstuctor1() {
    MyExpression exp = new MyExpression("a","anexp");
    RegExpStruct eg = new RegExpStruct(exp);
    assertEquals (eg.getGroupObj().get("a"), exp);
    assertEquals (eg.getExp(), exp.getKind().getReg());
    assertEquals (eg.getTotalPositions(),1);
  }
  /**
   * Test object constructor.
   */
  public final void testConstuctor2() {

    RegExpStruct eg = new RegExpStruct("string");
    assertEquals (eg.getExp(), "string");
    assertEquals (eg.getTotalPositions(),0);
  } 

  

  /**
   * Test add method for CHOICE  and string RegExpStructs.
   */
  public final void testAdd1() {;
   
    
    RegExpStruct eg = new RegExpStruct("a");
    RegExpStruct eg2 = new RegExpStruct("b");
    RegExpStruct choice = new RegExpStruct(RegType.CHOICE);
    choice.add(eg);
    choice.add(eg2);
    
    assertEquals(choice.getGroupObj(),new LinkedHashMap<String,Object>());
    assertEquals(choice.getExp(),"(?:a|b)");
    assertEquals (choice.getTotalPositions(),0);
    

  }
  

  /**
   * Test add method for CHOICE,string & MyObject RegExpStructs.
   */
  public final void testAdd2() {
    MyExpression exp = new MyExpression("a","anexp");
    MyExpression exp2 = new MyExpression("b","anexp");
    
    RegExpStruct eg = new RegExpStruct(exp);
    RegExpStruct eg2 = new RegExpStruct(exp2);
    RegExpStruct eg3 = new RegExpStruct("hi");
    RegExpStruct choice = new RegExpStruct(RegType.CHOICE);
    choice.add(eg);
    choice.add(eg2);
    choice.add(eg3);
    
    LinkedHashMap<String, Object> t = new LinkedHashMap<String, Object>();
    t.put(exp.getId(), exp);
    t.put(exp2.getId(), exp2);
    
    assertEquals(choice.getGroupObj(),t);
    assertEquals(choice.getExp(),"(?:"+exp.getKind().getReg()+"|"+exp.getKind().getReg()+"|"+"hi"+")");
    assertEquals (choice.getTotalPositions(), 2);
  }

  /**
   * Test add method for OPTIONAL  and string RegExpStructs.
   */
  public final void testAdd3() {;
   
    RegExpStruct eg = new RegExpStruct("a");
    RegExpStruct eg2 = new RegExpStruct("b");
    RegExpStruct choice = new RegExpStruct(RegType.OPTIONAL);
    choice.add(eg);
    choice.add(eg2);
    
    assertEquals(choice.getGroupObj(),new LinkedHashMap<String,Object>());
    assertEquals(choice.getExp(),"(?:a"+space+"b)?");
    assertEquals (choice.getTotalPositions(),0);
    

  }
  

  /**
   * Test add method for OPTIONAL,string & MyObject RegExpStructs.
   */
  public final void testAdd4() {
    MyExpression exp = new MyExpression("a","anexp");
    MyExpression exp2 = new MyExpression("b","anexp");
    
    RegExpStruct eg = new RegExpStruct(exp);
    RegExpStruct eg2 = new RegExpStruct(exp2);
    RegExpStruct eg3 = new RegExpStruct("hi");
    RegExpStruct choice = new RegExpStruct(RegType.OPTIONAL);
    choice.add(eg);
    choice.add(eg2);
    choice.add(eg3);
    
    LinkedHashMap<String, Object> t = new LinkedHashMap<String, Object>();
    t.put(exp.getId(), exp);
    t.put(exp2.getId(), exp2);
    
    assertEquals(choice.getGroupObj(),t);
    assertEquals(choice.getExp(),"(?:"+exp.getKind().getReg()+space+exp.getKind().getReg()+space+"hi"+")?");
    assertEquals (choice.getTotalPositions(), 2);
  }
  
  /**
   * Test add method for NORMAL and string RegExpStructs.
   */
  public final void testAdd5() {;
   
    RegExpStruct eg = new RegExpStruct();
    RegExpStruct eg1 = new RegExpStruct("a");
    RegExpStruct eg2 = new RegExpStruct("b");
    eg.add(eg1);
    eg.add(eg2);
    
    assertEquals(eg.getGroupObj(),new LinkedHashMap<String,Object>());
    assertEquals(eg.getExp(),"a"+space+"b");
    assertEquals (eg.getTotalPositions(),0);
    

  }
  

  /**
   * Test add method for NORMAL,string & MyObject RegExpStructs.
   */
  public final void testAdd6() {
    MyExpression exp = new MyExpression("a","anexp");
    MyExpression exp2 = new MyExpression("b","anexp");
    
    RegExpStruct eg = new RegExpStruct(exp);
    RegExpStruct eg2 = new RegExpStruct(exp2);
    RegExpStruct eg3 = new RegExpStruct("hi");
    
    eg.add(eg2);
    eg.add(eg3);
    
    LinkedHashMap<String, Object> t = new LinkedHashMap<String, Object>();
    t.put(exp.getId(), exp);
    t.put(exp2.getId(), exp2);
    
    assertEquals(eg.getGroupObj(),t);
    assertEquals(eg.getExp(),""+exp.getKind().getReg()+space+exp.getKind().getReg()+space+"hi"+"");
    assertEquals (eg.getTotalPositions(), 2);
  }

  /**
   * Test add method for NORMAL,OPTIONAL,CHOICE,string & MyObject RegExpStructs.
   */
  public final void testAdd7() {
    MyExpression exp = new MyExpression("a","anexp");
    MyDescription exp2 = new MyDescription("b","anexp");
    MyExpression exp3 = new MyExpression("c","anexp");
    MyDescription exp4 = new MyDescription("d","anexp");
    MyExpression exp5 = new MyExpression("e","anexp");
    MyDescription exp6 = new MyDescription("f","anexp");
    MyExpression exp7 = new MyExpression("g","anexp");
    MyDescription exp8 = new MyDescription("h","anexp");
    
    
    RegExpStruct optional = new RegExpStruct(RegType.OPTIONAL);
    RegExpStruct choice = new RegExpStruct(RegType.CHOICE);
    RegExpStruct eg = new RegExpStruct(exp);
    RegExpStruct eg2 = new RegExpStruct(exp2);
    RegExpStruct eg3 = new RegExpStruct(exp3);
    RegExpStruct eg4 = new RegExpStruct(exp4);
    RegExpStruct eg5 = new RegExpStruct(exp5);
    RegExpStruct eg6 = new RegExpStruct(exp6);
    RegExpStruct eg7 = new RegExpStruct(exp7);
    RegExpStruct eg8 = new RegExpStruct(exp8);
    
   
    
    eg.add(eg2);
    eg.add(eg3);
    
    optional.add(eg4);
    optional.add(eg5);
    
    eg.add(optional);
    
    choice.add(eg6);
    choice.add(eg7);
    choice.add(eg8);
    
    eg.add(choice);
    
    
    LinkedHashMap<String, Object> t = new LinkedHashMap<String, Object>();
    t.put(exp.getId(), exp);
    t.put(exp2.getId(), exp2);
    t.put(exp3.getId(), exp3);
    t.put(exp4.getId(), exp4);
    t.put(exp5.getId(), exp5);
    t.put(exp6.getId(), exp6);
    t.put(exp7.getId(), exp7);
    t.put(exp8.getId(), exp8);
   
    String reg = 
    exp.getKind().getReg()+space+
    exp2.getKind().getReg()+space+
    exp3.getKind().getReg()+opSpace+
    "(?:"+exp4.getKind().getReg()+space+exp5.getKind().getReg()+")?"+space+
    "(?:"+exp6.getKind().getReg()+"|"+exp7.getKind().getReg()+"|"+exp8.getKind().getReg()+")"
    ;
    assertEquals(eg.getGroupObj(),t);
    assertEquals(eg.getExp(),reg);
    assertEquals (eg.getTotalPositions(), 8);
  }
  
  /**
   * Test the overriden testEquals method.
   */
  public final void testEqualsSimple() {
    String exp = "anexp";
    RegExpStruct eg1 = new RegExpStruct(exp);
    RegExpStruct eg2 = new RegExpStruct(exp);


    assertTrue(RegExpStruct.equals(eg1,eg2));
  }
  
  
  /**
   * Test the overriden testEquals method.
   */
  public final void testEqualsWithNonEmptyMaps() {

    MyExpression exp = new MyExpression("a","anexp");
    MyExpression exp2 = new MyExpression("a","anexp");
    
    RegExpStruct eg1 = new RegExpStruct(exp);
    RegExpStruct eg2 = new RegExpStruct(exp2);


    assertTrue(RegExpStruct.equals(eg1,eg2));
  }
  

}
