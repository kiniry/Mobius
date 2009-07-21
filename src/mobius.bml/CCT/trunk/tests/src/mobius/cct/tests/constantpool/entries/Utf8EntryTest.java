package mobius.cct.tests.constantpool.entries;

import static org.junit.Assert.assertArrayEquals;

import java.io.ByteArrayOutputStream;

import mobius.cct.constantpool.entries.Entry;
import mobius.cct.constantpool.entries.Utf8Entry;

import org.junit.Test;

/**
 * Tests for class mobius.cct.constantpool.entries.Utf8Entry.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class Utf8EntryTest extends AbstractEntryTest {

  @Override
  protected Entry getEntry() {
    return new Utf8Entry("TestTestTest");
  }

  @Override
  protected byte[] getSerialized() {
    return new byte[]{0, 12, 84, 101, 115, 116, 84, 101, 115, 116, 84, 101, 115, 116};
  }

  @Override
  protected int getSize() {
    return 1;
  }

  @Override
  protected int getType() {
    return Entry.CONSTANT_Utf8;
  } 
  
  /**
   * Test serialization of strings with null characters.
   */
  @Test
  public void testNullChar() throws Exception {
    ByteArrayOutputStream bos = new ByteArrayOutputStream();
    new Utf8Entry("\0\0").write(bos);
    assertArrayEquals(new byte[]{0, 4, -64, -128, -64, -128}, 
                      bos.toByteArray());
  }
}
