package mobius.cct.tests.cache;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import mobius.cct.cache.Cache;
import mobius.cct.cache.FIFOCache;

import org.junit.Test;

/**
 * Tests for class mobius.cct.cache.LIFOCache.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class FIFOCacheTest extends AbstractCacheTest {
  /**
   * Cache size.
   */
  private static final int fSize = 4; 

  /**
   * Initialize cache.
   */
  protected Cache<Object> getCache() {
    return new FIFOCache<Object>(fSize);
  }
  
  /**
   * Test update - cache size limit.
   */
  @Test
  public void testFIFOUpdate1() {
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
  public void testFIFOUpdate2() {
    int i;
    
    for (i = 0; i <= fSize; i++) {
      fCache.update(Integer.toString(i), this);
    }
    for (i = 1; i <= fSize; i++) {
      assertTrue(fCache.hasKey(Integer.toString(i)));
    }
    assertFalse(fCache.hasKey("0"));
  }

}
