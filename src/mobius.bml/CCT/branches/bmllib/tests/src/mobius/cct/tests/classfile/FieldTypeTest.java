package mobius.cct.tests.classfile;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.io.IOException;

import mobius.cct.classfile.types.FieldType;

import org.junit.Test;

/**
 * Tests for class mobius.cct.repositories.classfile.types.FieldType.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class FieldTypeTest {
  
  /**
   * Test array types.
   */
  @Test
  public void testArray() throws IOException {
    final FieldType t1 = FieldType.parse("[I");
    final FieldType t2 = FieldType.parse("[[[[I");
    assertNotNull(t1);
    assertNotNull(t2);
    assertTrue(t1.isArray());
    assertFalse(t1.isObject());
    assertFalse(t1.isPrimitive());
    assertTrue(t2.isArray());
    assertFalse(t2.isObject());
    assertFalse(t2.isPrimitive());
    assertEquals("[I", t1.internalForm());
    assertEquals("int[]", t1.externalForm());
    assertEquals("[[[[I", t2.internalForm());
    assertEquals("int[][][][]", t2.externalForm());
  }

  /**
   * Test object types.
   */
  @Test
  public void testObject() throws IOException {
    final FieldType t1 = FieldType.parse("Ljava/lang/Object;");
    final FieldType t2 = FieldType.parse("LTest;");
    assertNotNull(t1);
    assertNotNull(t2);
    assertFalse(t1.isArray());
    assertTrue(t1.isObject());
    assertFalse(t1.isPrimitive());
    assertFalse(t2.isArray());
    assertTrue(t2.isObject());
    assertFalse(t2.isPrimitive());
    assertEquals("Ljava/lang/Object;", t1.internalForm());
    assertEquals("java.lang.Object", t1.externalForm());
    assertEquals("LTest;", t2.internalForm());
    assertEquals("Test", t2.externalForm());
  }

  /**
   * Test primitive types.
   */
  @Test
  public void testPrimitive() throws IOException {
    testPrimitive("B", "byte");
    testPrimitive("C", "char");
    testPrimitive("D", "double");
    testPrimitive("F", "float");
    testPrimitive("I", "int");
    testPrimitive("J", "long");
    testPrimitive("S", "short");
    testPrimitive("Z", "boolean");
  }

  /**
   * Test invalid type - void.
   */
  @Test(expected=IOException.class)
  public void testVoid() throws IOException {
    FieldType.parse("V");
  }

  /**
   * Test invalid type - empty.
   */
  @Test(expected=IOException.class)
  public void testEmpty() throws IOException {
    FieldType.parse("");
  }
  
  /**
   * Test invalid type - "X".
   */
  @Test(expected=IOException.class)
  public void testUnknownType() throws IOException {
    FieldType.parse("X");
  }
  
  /**
   * Helper method - test given primitive type.
   * @param iname Internal form of type name
   * @param ename External form of type name..
   */
  private void testPrimitive(final String iname, 
                             final String ename) 
    throws IOException {
    final FieldType t = FieldType.parse(iname);
    assertNotNull(t);
    assertFalse(t.isArray());
    assertFalse(t.isObject());
    assertTrue(t.isPrimitive());
    assertEquals(iname, t.internalForm());
    assertEquals(ename, t.externalForm());
  }
}
