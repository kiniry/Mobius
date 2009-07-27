package mobius.cct.tests.constantpool.entries;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;

import java.io.ByteArrayOutputStream;

import mobius.cct.constantpool.entries.Entry;

import org.junit.Before;
import org.junit.Test;

/**
 * Common tests for all constant pool entries.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public abstract class AbstractEntryTest {
  /** Entry instance. */
  private Entry fEntry;
  
  /** Returns entry instance. */
  protected abstract Entry getEntry();
  
  /** Returns expected entry type. */
  protected abstract int getType();
  
  /** Returns expected entry size. */
  protected abstract int getSize();
  
  /** Returns expected result of entry serialization. */
  protected abstract byte[] getSerialized();
  
  /**
   * Method called by setUp().
   * Can be overloaded by subclasses.
   */
  protected void init() {}
  
  /**
   * Method called before each test.
   */
  @Before
  public final void setUp() {
    init();
    fEntry = getEntry();
  }
  
  /**
   * Test serialization.
   */
  @Test
  public void testWrite() throws Exception {
    ByteArrayOutputStream bos = new ByteArrayOutputStream();
    fEntry.write(bos);
    assertArrayEquals(getSerialized(), bos.toByteArray());
  }
  
  /**
   * Test constant type.
   */
  @Test
  public void testType() {
    assertEquals(getType(), fEntry.getType());
  }
  
  /**
   * Test size.
   */
  @Test
  public void testSize() {
    assertEquals(getSize(), fEntry.getSize());
  }
}
