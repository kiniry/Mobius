package mobius.cct.tests.repositories.cp.entries;

import mobius.cct.repositories.cp.entries.NameAndTypeEntry;
import mobius.cct.repositories.cp.entries.Entry;

/**
 * Tests for class mobius.cct.repositories.cp.entries.DoubleEntry.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class NameAndTypeEntryTest extends AbstractEntryTest {

  @Override
  protected Entry getEntry() {
    return new NameAndTypeEntry(42, 44);
  }

  @Override
  protected byte[] getSerialized() {
    return new byte[]{0x00, 42, 0x00, 44};
  }

  @Override
  protected int getSize() {
    return 1;
  }

  @Override
  protected int getType() {
    return Entry.CONSTANT_NameAndType;
  } 
}
