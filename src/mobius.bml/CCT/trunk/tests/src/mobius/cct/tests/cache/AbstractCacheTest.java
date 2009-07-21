package mobius.cct.tests.cache;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import mobius.cct.cache.Cache;

import org.junit.Before;
import org.junit.Test;

/**
 * Tests applicable to all cache implementations.
 * Caches are required to be able to store at least 
 * four elements.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public abstract class AbstractCacheTest {

  /**
   * Empty cache - recreated before each test.
   */
  protected Cache<Object> fCache;
  
  /**
   * This method should create empty cache instance and perform
   * test setup.
   */
  protected abstract Cache<Object> getCache();
  
  /**
   * Method run before each test.
   */
  @Before
  public final void setUp() {
    fCache = getCache();
  }
  
  /**
   * Test constructor. Cache should be empty.
   */
  @Test
  public void testCreate() {
    assertEquals(fCache.size(), 0);
  }
  
  /**
   * Test update - null as first argument.
   */
  @Test(expected = NullPointerException.class)
  public void testUpdate1() {
    fCache.update(null, this);
  }
  
  /**
   * Test update - null as second argument.
   */
  @Test(expected = NullPointerException.class)
  public void testUpdate2() {
    fCache.update("KEY", null);
  }
  
  /**
   * Test lookup - positive case.
   */
  @Test
  public void testLookup1() {
    fCache.update("KEY", this);
    assertEquals(fCache.lookup("KEY"), this);
  }
  
  /**
   * Test lookup - negative case.
   */
  @Test
  public void testLookup2() {
    fCache.update("KEY", this);
    assertNull(fCache.lookup("kEy")); // keys are case-sensitive
  }
  
  /** 
   * Test lookup - null key. 
   **/
  @Test
  public void testLookup3() {
    assertNull(fCache.lookup(null));
  }

  /** 
   * Test remove - key exists in cache. 
   **/
  @Test
  public void testRemove1() {
    fCache.update("KEY", this);
    fCache.remove("KEY");
    assertNull(fCache.lookup("KEY"));
    assertEquals(0, fCache.size());
  }

  /** 
   * Test remove - key not in cache. 
   **/
  @Test
  public void testRemove2() {
    fCache.update("KEY", this);
    fCache.remove("kEy");
    assertTrue(fCache.hasKey("KEY"));
  }
  
  /** 
   * Test remove - null key. 
   **/
  @Test
  public void testRemove3() {
    fCache.update("KEY", this);
    fCache.remove(null);
    assertTrue(fCache.hasKey("KEY"));
  }
  
  /** 
   * Test hasKey - key exists in cache. 
   **/
  public void testHasKey1() {
    fCache.update("KEY", this);
    assertTrue(fCache.hasKey("KEY"));
  }

  /** 
   * Test hasKey - key not in cache. 
   **/
  @Test
  public void testHasKey2() {
    fCache.update("KEY", this);
    assertFalse(fCache.hasKey("kEy"));
  }

  /** 
   * Test hasKey - key was removed from cache. 
   **/
  @Test
  public void testHasKey3() {
    fCache.update("KEY", this);
    fCache.remove("KEY");
    assertFalse(fCache.hasKey("KEY"));
  }
  
  /** 
   * Test hasKey - null key. 
   **/
  @Test
  public void testHasKey4() {
    assertFalse(fCache.hasKey(null));
  }
  
  /**
   * Test size.
   */
  @Test
  public void testSize() {
    fCache.update("KEY1", this);
    assertEquals(1, fCache.size());
    fCache.update("KEY2", this);
    assertEquals(2, fCache.size());
    fCache.remove("KEY1");
    assertEquals(1, fCache.size());
  }
  
}
