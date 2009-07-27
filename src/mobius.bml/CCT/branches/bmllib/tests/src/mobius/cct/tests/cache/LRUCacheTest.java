package mobius.cct.tests.cache;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import mobius.cct.cache.Cache;
import mobius.cct.cache.LRUCache;

import org.junit.Test;

/**
 * Tests for class mobius.cct.cache.LRUCache.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class LRUCacheTest extends AbstractCacheTest {
  /**
   * Cache size.
   */
  private static final int fSize = 4; 

  /**
   * Initialize cache.
   */
  protected Cache<Object> getCache() {
    return new LRUCache<Object>(fSize);
  }
  
  /**
   * Test update - cache size limit.
   */
  @Test
  public void testLRUUpdate1() {
    int i;
    
    for (i = 0; i < 2 * fSize; i++) {
      fCache.update(Integer.toString(i), this);
    }
    assertEquals(fSize, fCache.size());
  }

  /**
   * Test update - objects removed during update.
   */
  @Test
  public void testLRUUpdate2() {
    int i;
    
    for (i = 0; i <= fSize; i++) {
      fCache.update(Integer.toString(i), this);
    }
    for (i = 1; i <= fSize; i++) {
      assertTrue(fCache.hasKey(Integer.toString(i)));
    }
    assertFalse(fCache.hasKey("0"));
  }

  /**
   * Test lookup - lookup should affect choice of object
   * to be removed from cache.
   */
  @Test
  public void testLRULookup() {
    int i;
    
    for (i = 0; i < fSize; i++) {
      fCache.update(Integer.toString(i), this);
    }
    for (i = 0; i < fSize; i++) {
      fCache.lookup(Integer.toString(fSize - i - 1));
    }
    fCache.update("KEY", this);
    for (i = 0; i < fSize - 1; i++) {
      assertTrue(fCache.hasKey(Integer.toString(i)));
    }
    assertTrue(fCache.hasKey("KEY"));
    assertFalse(fCache.hasKey(Integer.toString(fSize - 1)));
  }

  /**
   * Test hasKey - lookup should affect choice of object
   * to be removed from cache.
   */
  @Test
  public void testLRUHasKey() {
    int i;
    
    for (i = 0; i < fSize; i++) {
      fCache.update(Integer.toString(i), this);
    }
    for (i = 0; i < fSize; i++) {
      fCache.hasKey(Integer.toString(fSize - i - 1));
    }
    fCache.update("KEY", this);
    for (i = 0; i < fSize - 1; i++) {
      assertTrue(fCache.hasKey(Integer.toString(i)));
    }
    assertTrue(fCache.hasKey("KEY"));
    assertFalse(fCache.hasKey(Integer.toString(fSize - 1)));
  }
  
}
