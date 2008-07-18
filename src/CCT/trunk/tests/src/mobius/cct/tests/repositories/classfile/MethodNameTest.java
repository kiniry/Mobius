package mobius.cct.tests.repositories.classfile;

import java.io.IOException;

import mobius.cct.repositories.classfile.MethodName;
import mobius.cct.repositories.classfile.types.ByteType;
import mobius.cct.repositories.classfile.types.FieldType;
import mobius.cct.repositories.classfile.types.IntType;
import mobius.cct.repositories.classfile.types.VoidType;

import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Tests for class MethodName.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MethodNameTest {

  /**
   * Test method with no arguments and void result.
   */
  @Test
  public void testVoidNoArgs() {
    final MethodName m = new MethodName("test", 
                                        new FieldType[]{}, 
                                        VoidType.getInstance());
    assertEquals("void test()", m.externalForm());
    assertEquals("test()V", m.internalForm());
  }

  /**
   * Test method with single argument and void result.
   */
  @Test
  public void testVoidSingleArg() {
    final MethodName m = 
      new MethodName("test", 
                     new FieldType[]{IntType.getInstance()}, 
                     VoidType.getInstance());
    assertEquals("void test(int)", m.externalForm());
    assertEquals("test(I)V", m.internalForm());
  }

  /**
   * Test method with three arguments and void result.
   */
  @Test
  public void testVoidThreeArgs() {
    final MethodName m = 
      new MethodName("test", 
                     new FieldType[] {
                                      IntType.getInstance(),
                                      ByteType.getInstance(),
                                      ByteType.getInstance(),
                                     }, 
                     VoidType.getInstance());
    assertEquals("void test(int, byte, byte)", m.externalForm());
    assertEquals("test(IBB)V", m.internalForm());
  }

  /**
   * Test method with three arguments and integer result.
   */
  @Test
  public void testIntThreeArgs() {
    final MethodName m = 
      new MethodName("test", 
                     new FieldType[] {
                                      IntType.getInstance(),
                                      ByteType.getInstance(),
                                      ByteType.getInstance(),
                                     }, 
                     IntType.getInstance());
    assertEquals("int test(int, byte, byte)", m.externalForm());
    assertEquals("test(IBB)I", m.internalForm());
  }
  
  /**
   * Test parsing.
   */
  @Test
  public void testParse() throws Exception {
    p("()V");
    p("(I)V");
    p("(IBB)V");
    p("(IBB)I");
  }
  
  /**
   * Test parsing of erroneous types - void argument.
   */
  @Test(expected=IOException.class)
  public void testParseError1() throws IOException {
    p("(V)V");
  }

  /**
   * Test parsing of erroneous types - invalid format.
   */
  @Test(expected=IOException.class)
  public void testParseError2() throws IOException {
    p("II)V");
  }

  /**
   * Test parsing of erroneous types - invalid format.
   */
  @Test(expected=IOException.class)
  public void testParseError3() throws IOException {
    p("(IIV");
  }
  
  /**
   * Test parsing of given string.
   * @param s String to test.
   */
  private void p(final String s) throws IOException {
    assertEquals(s, MethodName.parse(s).internalForm());
  }
}
