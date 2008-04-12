package mobius.cct.tests.cache;

import mobius.cct.cache.Cache;
import mobius.cct.cache.InfiniteCache;

/**
 * Tests for class mobius.cct.cache.InfiniteCache.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class InfiniteCacheTest extends AbstractCacheTest {
  /**
   * Initialize cache.
   */
  protected Cache<Object> getCache() {
    return new InfiniteCache<Object>();
  }
}
