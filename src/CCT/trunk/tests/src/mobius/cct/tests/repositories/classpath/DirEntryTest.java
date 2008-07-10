package mobius.cct.tests.repositories.classpath;

import java.io.File;
import java.io.InputStream;

import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.*;

import mobius.cct.repositories.Resource;
import mobius.cct.repositories.classpath.DirEntry;
import mobius.cct.repositories.NotFoundException;
import mobius.cct.tests.testutil.Util;

/**
 * Tests fpr class mobius.cct.repositories.classpath.DirEntry.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DirEntryTest {  
  /**
   * Entry used in tests.
   */
  private DirEntry fEntry;
  
  /**
   * Method called before each test.
   */
  @Before
  public void setUp() {
    fEntry = new DirEntry(new File("./tests/data"));
  }
  
  /**
   * Test loading of a class - positive case.
   */
  @Test
  public void testClass1() throws Exception {
    Resource r = fEntry.getClassFile("mobius.cct.testdata.Test1");
    assertNotNull(r);
    InputStream is = r.open();
    assertNotNull(is);
    assertEquals("12872b2fb305213f2c7adac2a945f3da", 
                 Util.toHex(Util.digest(is, Util.MD5)));
    is.close();
  }
  
  /**
   * Test loading of a class - class not found.
   */
  @Test(expected=NotFoundException.class)
  public void testClass2() throws Exception {
    fEntry.getClassFile("mobius.cct.testdata.FalseTest");
  }
  
}
