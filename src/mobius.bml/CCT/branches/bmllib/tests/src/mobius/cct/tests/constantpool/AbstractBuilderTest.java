package mobius.cct.tests.constantpool;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;
import mobius.cct.constantpool.ConstantPool;
import mobius.cct.constantpool.ConstantPoolBuilder;
import mobius.cct.constantpool.ConstantPoolFactory;
import mobius.cct.constantpool.DefaultFactory;
import mobius.cct.constantpool.IllegalIndexException;
import mobius.cct.constantpool.entries.ClassEntry;
import mobius.cct.constantpool.entries.DoubleEntry;
import mobius.cct.constantpool.entries.Entry;
import mobius.cct.constantpool.entries.FloatEntry;
import mobius.cct.constantpool.entries.IntegerEntry;
import mobius.cct.constantpool.entries.LongEntry;
import mobius.cct.constantpool.entries.StringEntry;
import mobius.cct.constantpool.entries.Utf8Entry;

import org.junit.Before;
import org.junit.Test;

/**
 * Generic tests for all implementations of ConstantPoolBuilder interface.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public abstract class AbstractBuilderTest {
  /**
   * Builder instance.
   */
  protected ConstantPoolBuilder fBuilder;
  
  /**
   * Constant pool factory (mock object would be better...).
   */
  protected ConstantPoolFactory fFactory;
  
  /** 
   * This method should create builder instance.
   * It will be called once before each test.
   */
  protected abstract ConstantPoolBuilder getBuilder();
  
  /**
   * Method called before each test.
   */
  @Before
  public final void setUp() {
    fBuilder = getBuilder();
    fFactory = new DefaultFactory();
  }
  
  /**
   * Test empty builder behavior.
   */
  @Test
  public void testEmpty() {
    assertEquals(0, fBuilder.toConstantPool(fFactory).getSize());
  }
  
  /**
   * Test Class constant addition.
   */
  @Test
  public void testClass() {
    int c = fBuilder.newClass("java/lang/Object");
    ConstantPool cp = fBuilder.toConstantPool(fFactory);
    try {
      assertEquals(Entry.CONSTANT_Class, cp.getEntry(c).getType());
      ClassEntry e = (ClassEntry)cp.getEntry(c);
      assertEquals(Entry.CONSTANT_Utf8, cp.getEntry(e.getName()).getType());
      Utf8Entry e2 = (Utf8Entry)cp.getEntry(e.getName());
      assertEquals("java/lang/Object", e2.getValue());
    } catch (IllegalIndexException e) {
      fail("IllegalIndexException");
    }
  }
  
  /**
   * Test String constant addition.
   */
  @Test
  public void testString() {
    int c = fBuilder.newString("TestTestTest");
    ConstantPool cp = fBuilder.toConstantPool(fFactory);
    try {
      assertEquals(Entry.CONSTANT_String, cp.getEntry(c).getType());
      StringEntry e = (StringEntry)cp.getEntry(c);
      assertEquals(Entry.CONSTANT_Utf8, cp.getEntry(e.getValue()).getType());
      Utf8Entry e2 = (Utf8Entry)cp.getEntry(e.getValue());
      assertEquals("TestTestTest", e2.getValue());
    } catch (IllegalIndexException e) {
      fail("IllegalIndexException");
    }
  }
  
  /**
   * Test Utf8 constant addition.
   */
  @Test
  public void testUtf8() {
    int c = fBuilder.newUtf8("TestTestTest");
    ConstantPool cp = fBuilder.toConstantPool(fFactory);
    try {
      assertEquals(Entry.CONSTANT_Utf8, cp.getEntry(c).getType());
      Utf8Entry e = (Utf8Entry)cp.getEntry(c);
      assertEquals("TestTestTest", e.getValue());
    } catch (IllegalIndexException e) {
      fail("IllegalIndexException");
    }
  }
  
  /**
   * Test Integer constant addition.
   */
  @Test
  public void testInteger() {
    int c = fBuilder.newInt(42);
    ConstantPool cp = fBuilder.toConstantPool(fFactory);
    try {
      assertEquals(Entry.CONSTANT_Integer, cp.getEntry(c).getType());
      IntegerEntry e = (IntegerEntry)cp.getEntry(c);
      assertEquals(42, e.getValue());
    } catch (IllegalIndexException e) {
      fail("IllegalIndexException");
    }
  }

  /**
   * Test Long constant addition.
   */
  @Test
  public void testLong() {
    int c = fBuilder.newLong(42);
    ConstantPool cp = fBuilder.toConstantPool(fFactory);
    try {
      assertEquals(Entry.CONSTANT_Long, cp.getEntry(c).getType());
      LongEntry e = (LongEntry)cp.getEntry(c);
      assertEquals(42, e.getValue());
    } catch (IllegalIndexException e) {
      fail("IllegalIndexException");
    }
  }
  
  /**
   * Test Float constant addition.
   */
  @Test
  public void testFloat() {
    int c = fBuilder.newFloat(42.0f);
    ConstantPool cp = fBuilder.toConstantPool(fFactory);
    try {
      assertEquals(Entry.CONSTANT_Float, cp.getEntry(c).getType());
      FloatEntry e = (FloatEntry)cp.getEntry(c);
      assertEquals(42.0f, e.getValue(), 0.0);
    } catch (IllegalIndexException e) {
      fail("IllegalIndexException");
    }
  }
  
  /**
   * Test Double constant addition.
   */
  @Test
  public void testDouble() {
    int c = fBuilder.newDouble(42.0);
    ConstantPool cp = fBuilder.toConstantPool(fFactory);
    try {
      assertEquals(Entry.CONSTANT_Double, cp.getEntry(c).getType());
      DoubleEntry e = (DoubleEntry)cp.getEntry(c);
      assertEquals(42.0, e.getValue(), 0.0);
    } catch (IllegalIndexException e) {
      fail("IllegalIndexException");
    }
  }
}
