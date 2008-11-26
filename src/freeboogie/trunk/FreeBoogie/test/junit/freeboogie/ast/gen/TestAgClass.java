package freeboogie.ast.gen;

import org.junit.*;


/**
 * Represents a class from the abstract grammar.
 * 
 * @author Mikolas Janota 
 */
public class TestAgClass {

  private AgClass base, c;
  private AgMember baseMemeber, cMember;

  @Before public void setup() {
    c = new AgClass();
    base = new AgClass();
    c.setBaseClass(base);

    baseMemeber = new AgMember();
    cMember = new AgMember();
    base.addMember(baseMemeber);
    c.addMember(cMember);
  }

  @Test public void testMembers() {
    Assert.assertTrue("The base class members should be returnded by members.",
                      c.getMembers().contains(baseMemeber));
  }
                    
  @Test public void testInheritedMembers() {
    Assert.assertTrue("The base class members should not be returnded by selfmembers.",
                       c.getInheritedMembers().contains(baseMemeber));
    Assert.assertFalse("The base class members should not be returnded by selfmembers.",
                       c.getInheritedMembers().contains(cMember));
  }
                    
  @Test public void testSelfMembers() {
    Assert.assertFalse("The base class members should not be returnded by selfmembers.",
                       c.getSelfMembers().contains(baseMemeber));
    Assert.assertTrue(c.getSelfMembers().contains(cMember));
  }

  
}
