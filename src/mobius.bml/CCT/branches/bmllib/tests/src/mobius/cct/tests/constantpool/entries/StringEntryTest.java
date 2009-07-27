package mobius.cct.tests.constantpool.entries;

import mobius.cct.constantpool.entries.Entry;
import mobius.cct.constantpool.entries.StringEntry;

/**
 * Tests for class mobius.cct.constantpool.entries.StringEntry.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class StringEntryTest extends AbstractEntryTest {

  @Override
  protected Entry getEntry() {
    return new StringEntry(42);
  }

  @Override
  protected byte[] getSerialized() {
    return new byte[]{0x00, 42};
  }

  @Override
  protected int getSize() {
    return 1;
  }

  @Override
  protected int getType() {
    return Entry.CONSTANT_String;
  } 
}
