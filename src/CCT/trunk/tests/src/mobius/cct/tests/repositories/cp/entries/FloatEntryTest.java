package mobius.cct.tests.repositories.cp.entries;

import mobius.cct.repositories.cp.entries.FloatEntry;
import mobius.cct.repositories.cp.entries.Entry;

/**
 * Tests for class mobius.cct.repositories.cp.entries.FloatEntry.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class FloatEntryTest extends AbstractEntryTest {

  @Override
  protected Entry getEntry() {
    return new FloatEntry(42.0f);
  }

  @Override
  protected byte[] getSerialized() {
    return new byte[]{66, 40, 0, 0};
  }

  @Override
  protected int getSize() {
    return 1;
  }

  @Override
  protected int getType() {
    return Entry.CONSTANT_Float;
  } 
}
