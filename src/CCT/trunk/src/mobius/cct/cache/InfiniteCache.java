package mobius.cct.cache;

import java.util.HashMap;
import java.util.Map;

/**
 * Infinite 'cache' - dictionary wrapped in cache interface.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <C> Type of cached objects.
 */
public class InfiniteCache<C> implements Cache<C> {
  /** Map. */
  private final Map<String, C> fMap;
  
  /**
   * Create cache.
   */
  public InfiniteCache() {
    fMap = new HashMap<String, C>();
  }
  
  /**
   * Add new object to cache or update existing binding.
   * Objects are never removed during update.
   * @param key Key (non-null).
   * @param object Object to be stored. Cannot be {@code null}. 
   */
  @Override
  public void update(final String key, final C object) {
    if ((key == null) || (object == null)) {
      throw new IllegalArgumentException();
    }
    fMap.put(key, object);
  }
  
  /**
   * Remove binding for given key from cache (if present).
   * @param key Key. Does not have to be bound.
   */
  @Override
  public void remove(final String key) {
    fMap.remove(key);
  }
    
  /**
   * Retrieve object from cache.
   * @param key Key (possibly null).
   * @return Retrieved value or {@code null} (if the key
   * is not bound in cache).
   */
  @Override
  public C lookup(final String key) {
    return fMap.get(key);
  }
  
  /**
   * Check if there is a binding for given key in the cache.
   * @param key Key (possibly null).
   * @return {@code true} iff key is bound in the cache.
   */
  @Override
  public boolean hasKey(final String key) {
    return fMap.containsKey(key);
  }
  
  /**
   * Get number of objects in the cache.
   * @return cache size.
   */
  @Override
  public int size() {
    return fMap.size();
  }
}
