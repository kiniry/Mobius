package mobius.cct.tests.cache;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import mobius.cct.cache.LIFOCache;

import org.junit.Test;

/**
 * Tests for class mobius.cct.cache.LIFOCache.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class LIFOCacheTest extends AbstractCacheTest {
  /**
   * Cache size.
   */
  private static final int fSize = 4; 

  /**
   * Initialize cache.
   */
  protected void initCache() {
    fCache = new LIFOCache<Object>(fSize);
  }
  
  /**
   * Test update - cache size limit.
   */
  @Test
  public void testLIFOUpdate1() {
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
  public void testLIFOUpdate2() {
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
