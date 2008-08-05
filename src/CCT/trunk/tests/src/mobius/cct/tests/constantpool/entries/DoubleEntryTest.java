package mobius.cct.tests.constantpool.entries;

import mobius.cct.constantpool.entries.DoubleEntry;
import mobius.cct.constantpool.entries.Entry;

/**
 * Tests for class mobius.cct.constantpool.entries.DoubleEntry.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DoubleEntryTest extends AbstractEntryTest {

  @Override
  protected Entry getEntry() {
    return new DoubleEntry(42.0);
  }

  @Override
  protected byte[] getSerialized() {
    return new byte[]{64, 69, 0, 0, 0, 0, 0, 0};
  }

  @Override
  protected int getSize() {
    return 2;
  }

  @Override
  protected int getType() {
    return Entry.CONSTANT_Double;
  } 
}
