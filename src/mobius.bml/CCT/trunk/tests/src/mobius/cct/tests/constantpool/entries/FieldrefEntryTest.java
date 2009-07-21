package mobius.cct.tests.constantpool.entries;

import mobius.cct.constantpool.entries.Entry;
import mobius.cct.constantpool.entries.FieldrefEntry;

/**
 * Tests for class mobius.cct.constantpool.entries.FieldrefEntry.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class FieldrefEntryTest extends AbstractEntryTest {

  @Override
  protected Entry getEntry() {
    return new FieldrefEntry(42, 44);
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
    return Entry.CONSTANT_Fieldref;
  } 
}
