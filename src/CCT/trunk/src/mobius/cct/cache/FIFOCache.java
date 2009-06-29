package mobius.cct.cache;

import java.util.HashMap;
import java.util.Map;

import mobius.cct.util.ArrayQueue;

/**
 * Cache implementation using FIFO queue.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <C> Type of cached objects.
 */
public class FIFOCache<C> implements Cache<C> {
  /**
   * Queue of keys.
   */
  private final ArrayQueue<String> fKeys;
  
  /**
   * Mapping from keys to stored objects.
   */
  private final Map<String, C> fMap;
  
  /**
   * Cache size.
   */
  private int fSize;
  
  /**
   * Create cache with given size.
   * @param size Maximum number of objects in the cache.
   */
  public FIFOCache(final int size) {
    fKeys = new ArrayQueue<String>();
    fMap = new HashMap<String, C>();
    fSize = size;
  }
  
  /**
   * Add new object to cache or update existing binding.
   * If cache limit is exceeded, oldest binding is removed.
   * @param key Key.
   * @param object Object to be stored.
   */
  public void update(final String key, final C object) {
    if ((key == null) || (object == null)) {
      throw new NullPointerException();
    }
    if (!fMap.containsKey(key)) {
      if (fKeys.size() >= fSize) {
        final String oldKey = fKeys.poll();
        fMap.remove(oldKey);
      }
      fKeys.add(key);
    }
    fMap.put(key, object);
  }
  
  /**
   * Remove binding for given key from cache (if present).
   * @param key Key. Does not have to be bound.
   */
  public void remove(final String key) {
    fMap.remove(key);
    fKeys.remove(key);
  }
  
  /**
   * Retrieve object from cache.
   * @param key Key.
   * @return Retrieved value or {@code null} (if the key
   * is not bound in cache).
   */
  public C lookup(final String key) {
    return fMap.get(key);
  }
  
  /**
   * Check if there is a binding for given key in the cache.
   * @param key Key
   * @return {@code true} iff key is bound in the cache.
   */
  public boolean hasKey(final String key) {
    return fMap.containsKey(key);
  }
  
  /**
   * Get number of objects in the cache.
   * @return cache size.
   */
  public int size() {
    return fKeys.size();
  }
}
