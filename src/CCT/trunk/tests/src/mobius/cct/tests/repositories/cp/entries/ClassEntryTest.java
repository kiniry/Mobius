package mobius.cct.tests.repositories.cp.entries;

import mobius.cct.repositories.cp.entries.ClassEntry;
import mobius.cct.repositories.cp.entries.Entry;

/**
 * Tests for class mobius.cct.repositories.cp.entries.ClassEntry.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class ClassEntryTest extends AbstractEntryTest {

  @Override
  protected Entry getEntry() {
    return new ClassEntry(42);
  }

  @Override
  protected byte[] getSerialized() {
    return new byte[]{0, 42};
  }

  @Override
  protected int getSize() {
    return 1;
  }

  @Override
  protected int getType() {
    return Entry.CONSTANT_Class;
  } 
}
