package mobius.cct.tests.repositories.cp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;
import mobius.cct.repositories.cp.ConstantPool;
import mobius.cct.repositories.cp.ConstantPoolBuilder;
import mobius.cct.repositories.cp.DefaultBuilder;
import mobius.cct.repositories.cp.IllegalIndexException;
import mobius.cct.repositories.cp.entries.ClassEntry;
import mobius.cct.repositories.cp.entries.StringEntry;

import org.junit.Test;

/**
 * Tests for class mobius.cct.repositories.cp.DefaultBuilder
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultBuilderTest extends AbstractBuilderTest {

  /**
   * Create builder instance.
   */
  @Override
  protected ConstantPoolBuilder getBuilder() {
    return new DefaultBuilder();
  }

  /**
   * DefaultBuilder should avoid creating duplicates.
   */
  @Test
  public void testDuplicates() {
    int c1 = fBuilder.newString("Test");
    int c2 = fBuilder.newUtf8("Test");
    int c3 = fBuilder.newString("Test");
    int c4 = fBuilder.newClass("Test");
    ConstantPool cp = fBuilder.toConstantPool(fFactory);
    assertEquals(3, cp.getSize());
    assertEquals(c1, c3);
    try {
      assertEquals(((StringEntry)cp.getEntry(c1)).getValue(), c2);
      assertEquals(c2, ((ClassEntry)cp.getEntry(c4)).getName());
    } catch (IllegalIndexException e) {
      fail("IllegalIndexException");
    }
  }
  
}
