package mobius.cct.tests.repositories.cp.entries;

import mobius.cct.repositories.cp.entries.Entry;
import mobius.cct.repositories.cp.entries.MethodrefEntry;

/**
 * Tests for class mobius.cct.repositories.cp.entries.MethodrefEntry.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MethodrefEntryTest extends AbstractEntryTest {

  @Override
  protected Entry getEntry() {
    return new MethodrefEntry(42, 44);
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
    return Entry.CONSTANT_Methodref;
  } 
}
