package mobius.cct.tests.constantpool;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.fail;

import java.io.FileInputStream;
import java.io.IOException;

import mobius.cct.constantpool.ConstantPool;
import mobius.cct.constantpool.DefaultFactory;
import mobius.cct.constantpool.IllegalIndexException;
import mobius.cct.constantpool.InvalidIndexException;
import mobius.cct.constantpool.UnusableIndexException;
import mobius.cct.constantpool.entries.ClassEntry;
import mobius.cct.constantpool.entries.DoubleEntry;
import mobius.cct.constantpool.entries.Entry;
import mobius.cct.constantpool.entries.FieldrefEntry;
import mobius.cct.constantpool.entries.FloatEntry;
import mobius.cct.constantpool.entries.IntegerEntry;
import mobius.cct.constantpool.entries.InterfaceMethodrefEntry;
import mobius.cct.constantpool.entries.LongEntry;
import mobius.cct.constantpool.entries.MethodrefEntry;
import mobius.cct.constantpool.entries.NameAndTypeEntry;
import mobius.cct.constantpool.entries.StringEntry;
import mobius.cct.constantpool.entries.Utf8Entry;

import org.junit.Before;
import org.junit.Test;

/**
 * Tests for DefaultFactory and DefaultPool.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultFactoryTest {
  /**
   * Factory instance.
   */
  private DefaultFactory fFactory;
  
  /**
   * Array of entries used in sample pool.
   */
  private Entry[] fEntries;
  
  /**
   * Method called before each tests.
   */
  @Before
  public void setUp() {
    fFactory = new DefaultFactory();
    fEntries = 
      new Entry[] {
                   new Utf8Entry("mobius/cct/testdata/Test10"),  // 1
                   new ClassEntry(1),  // 2
                   new Utf8Entry("java/lang/Object"),  // 3 
                   new ClassEntry(3),  // 4
                   new Utf8Entry("<init>"),  // 5
                   new Utf8Entry("()V"),  // 6
                   new NameAndTypeEntry(5, 6),  // 7
                   new MethodrefEntry(4, 7),  // 8
                   new Utf8Entry("Code"),  // 9
                   new DoubleEntry(42.0),  // 10
                   new Utf8Entry("java/lang/Boolean"),  // 12
                   new ClassEntry(12),  // 13
                   new Utf8Entry("TRUE"),  // 14
                   new Utf8Entry("Z"),  // 15
                   new NameAndTypeEntry(14, 15), //  16
                   new FieldrefEntry(13, 16),  // 17 
                   new FloatEntry(42.0f),  //  18
                   new IntegerEntry(42),   //  19
                   new Utf8Entry("java/lang/Runnable"),  // 20
                   new ClassEntry(20),  // 21
                   new Utf8Entry("run"),  // 22
                   new Utf8Entry("()V"),  // 23
                   new NameAndTypeEntry(22, 23),  // 24
                   new InterfaceMethodrefEntry(21, 24),  // 25 
                   new LongEntry(42),  // 26
                   null, null, null, null, null,
                   new StringEntry(1),  // 28
    };
  }
  
  /**
   * Test constant pool created from array.
   */
  @Test
  public void testCreate1() {
    ConstantPool cp = fFactory.create(fEntries);
    assertEquals(28, cp.getSize());
    try {
      assertEquals(fEntries[0], cp.getEntry(1));
      assertEquals(fEntries[1], cp.getEntry(2));
      assertEquals(fEntries[2], cp.getEntry(3));
      assertEquals(fEntries[3], cp.getEntry(4));
      assertEquals(fEntries[4], cp.getEntry(5));
      assertEquals(fEntries[5], cp.getEntry(6));
      assertEquals(fEntries[6], cp.getEntry(7));
      assertEquals(fEntries[7], cp.getEntry(8));
      assertEquals(fEntries[8], cp.getEntry(9));
      assertEquals(fEntries[9], cp.getEntry(10));
      assertEquals(fEntries[10], cp.getEntry(12));
      assertEquals(fEntries[11], cp.getEntry(13));
      assertEquals(fEntries[12], cp.getEntry(14));
      assertEquals(fEntries[13], cp.getEntry(15));
      assertEquals(fEntries[14], cp.getEntry(16));
      assertEquals(fEntries[15], cp.getEntry(17));
      assertEquals(fEntries[16], cp.getEntry(18));
      assertEquals(fEntries[17], cp.getEntry(19));
      assertEquals(fEntries[18], cp.getEntry(20));
      assertEquals(fEntries[19], cp.getEntry(21));
      assertEquals(fEntries[20], cp.getEntry(22));
      assertEquals(fEntries[21], cp.getEntry(23));
      assertEquals(fEntries[22], cp.getEntry(24));
      assertEquals(fEntries[23], cp.getEntry(25));
      assertEquals(fEntries[24], cp.getEntry(26));
      assertEquals(fEntries[fEntries.length - 1], cp.getEntry(28));
    } catch (IllegalIndexException e) {
      fail("IllegalIndex");
    }
  }
  
  /**
   * Test unusable index in constant pool created from array.
   */
  @Test(expected=UnusableIndexException.class)
  public void testCreate2() throws Exception {
    ConstantPool cp = fFactory.create(fEntries);
    cp.getEntry(11);
  }
  
  /**
   * Test invalid index in constant pool created from array.
   */
  @Test(expected=InvalidIndexException.class)
  public void testCreate3() throws Exception {
    ConstantPool cp = fFactory.create(fEntries);
    cp.getEntry(0);
  }

  /**
   * Test another invalid index in constant pool created from array.
   */
  @Test(expected=InvalidIndexException.class)
  public void testCreate4() throws Exception {
    ConstantPool cp = fFactory.create(fEntries);
    cp.getEntry(29);
  }
  
  /**
   * Test reading of constant pool from stream.
   */
  @Test
  public void testRead() throws Exception {
    FileInputStream fs = new FileInputStream("./tests/data/SamplePool.bin");
    ConstantPool cp = null;
    try {
      cp = fFactory.read(fs);
    } catch (IOException e) {
      fail(e.toString());
    }
    fs.close();
    
    assertNotNull(cp);
    assertEquals(28, cp.getSize());
    try {
      assertEquals(fEntries[0], cp.getEntry(1));
      assertEquals(fEntries[1], cp.getEntry(2));
      assertEquals(fEntries[2], cp.getEntry(3));
      assertEquals(fEntries[3], cp.getEntry(4));
      assertEquals(fEntries[4], cp.getEntry(5));
      assertEquals(fEntries[5], cp.getEntry(6));
      assertEquals(fEntries[6], cp.getEntry(7));
      assertEquals(fEntries[7], cp.getEntry(8));
      assertEquals(fEntries[8], cp.getEntry(9));
      assertEquals(fEntries[9], cp.getEntry(10));
      assertEquals(fEntries[10], cp.getEntry(12));
      assertEquals(fEntries[11], cp.getEntry(13));
      assertEquals(fEntries[12], cp.getEntry(14));
      assertEquals(fEntries[13], cp.getEntry(15));
      assertEquals(fEntries[14], cp.getEntry(16));
      assertEquals(fEntries[15], cp.getEntry(17));
      assertEquals(fEntries[16], cp.getEntry(18));
      assertEquals(fEntries[17], cp.getEntry(19));
      assertEquals(fEntries[18], cp.getEntry(20));
      assertEquals(fEntries[19], cp.getEntry(21));
      assertEquals(fEntries[20], cp.getEntry(22));
      assertEquals(fEntries[21], cp.getEntry(23));
      assertEquals(fEntries[22], cp.getEntry(24));
      assertEquals(fEntries[23], cp.getEntry(25));
      assertEquals(fEntries[24], cp.getEntry(26));
      assertEquals(fEntries[fEntries.length - 1], cp.getEntry(28));
    } catch (IllegalIndexException e) {
      fail("IllegalIndex");
    }
  }
  
}
