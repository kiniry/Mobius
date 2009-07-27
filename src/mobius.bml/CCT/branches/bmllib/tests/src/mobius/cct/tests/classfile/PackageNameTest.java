package mobius.cct.tests.classfile;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import mobius.cct.classfile.PackageName;

import org.junit.Before;
import org.junit.Test;

/**
 * Tests for class mobius.cct.repositories.classfile.PackageName.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class PackageNameTest {
  /**
   * Root package
   */
  private PackageName root;
  
  /**
   * Method executed before each test.
   */
  @Before
  public void setUp() {
    root = PackageName.root();
  }
  /**
   * Test root package.
   */
  @Test
  public void testRoot() {
    assertNotNull(root);
    assertEquals("", root.internalForm());
    assertEquals("", root.externalForm());
    assertNull(root.getParent());
    assertTrue(root.isRoot());
  }
  
  /**
   * Test some simple package names.
   */
  @Test
  public void testPackage() {
    final PackageName p1 = PackageName.getPackage(root, "mobius");
    assertNotNull(p1);
    final PackageName p2 = PackageName.getPackage(p1, "cct");
    assertNotNull(p2);
    assertEquals("mobius", p1.internalForm());
    assertEquals("mobius", p1.externalForm());
    assertEquals("mobius/cct", p2.internalForm());
    assertEquals("mobius.cct", p2.externalForm());
    assertEquals(root, p1.getParent());
    assertEquals(p1, p2.getParent());
  }
}
