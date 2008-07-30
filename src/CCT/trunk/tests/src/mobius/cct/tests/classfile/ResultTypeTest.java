package mobius.cct.tests.classfile;

import static org.junit.Assert.assertEquals;
import mobius.cct.classfile.types.ResultType;

import org.junit.Test;

/**
 * Tests for class ResultType.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class ResultTypeTest {
  /**
   * Test parsing of void type.
   */
  @Test
  public void testVoid() throws Exception {
    final ResultType v = ResultType.parse("V");
    assertEquals("V", v.internalForm());
    assertEquals("void", v.externalForm());
  }
  
  // Other tests are in FieldTypeTest.java
}
