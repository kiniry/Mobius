package mobius.cct.cache;

/**
 * Cache implementation using LIFO queue.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <C> Type of cached objects.
 */
public class LIFOCache<C> implements Cache<C> {
  /**
   * Create cache with given size.
   * @param size Maximum number of objects in the cache.
   */
  public LIFOCache(final int size) {
  }
  
  /**
   * Add new object to cache or update existing binding.
   * If cache limit is exceeded, oldest binding is removed.
   * @param key Key.
   * @param object Object to be stored.
   */
  @Override
  public void update(final String key, final C object) {
  }
  
  /**
   * Remove binding for given key from cache (if present).
   * @param key Key. Does not have to be bound.
   * 
   */
  @Override
  public void remove(final String key) {
  }
  
  /**
   * Retrieve object from cache.
   * @param key Key.
   * @return Retrieved value or {@code null} (if the key
   * is not bound in cache).
   */
  @Override
  public C lookup(final String key) {
    return null;
  }
  
  /**
   * Check if there is a binding for given key in the cache.
   * @param key Key
   * @return {@code true} iff key is bound in the cache.
   */
  @Override
  public boolean hasKey(final String key) {
    return false;
  }
  
  /**
   * Get number of objects in the cache.
   * @return cache size.
   */
  public int size() {
    return 0;
  }
}
