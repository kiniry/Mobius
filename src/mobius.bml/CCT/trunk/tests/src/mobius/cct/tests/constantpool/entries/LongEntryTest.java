package mobius.cct.tests.constantpool.entries;

import mobius.cct.constantpool.entries.Entry;
import mobius.cct.constantpool.entries.LongEntry;

/**
 * Tests for class mobius.cct.constantpool.entries.LongEntry.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class LongEntryTest extends AbstractEntryTest {

  @Override
  protected Entry getEntry() {
    return new LongEntry(42);
  }

  @Override
  protected byte[] getSerialized() {
    return new byte[]{0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 42};
  }

  @Override
  protected int getSize() {
    return 2;
  }

  @Override
  protected int getType() {
    return Entry.CONSTANT_Long;
  } 
}
