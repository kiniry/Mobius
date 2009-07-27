package mobius.cct.cache;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Cache implementation using LRU algorithm.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <C> Type of cached objects.
 */
public class LRUCache<C> implements Cache<C> {
  /**
   * HashMap load factor.
   */
  private static final float LOAD_FACTOR = 0.75f;
  
  /**
   * Cache size.
   */
  private final int fSize;
  
  /**
   * Mapping from keys to elements.
   */
  private final LRUHashMap<String, C> fMap;
  
  /**
   * LinkedHashMap used to store cached elements.
   * @author Tadeusz Sznuk (ts209501@gmail.com)
   * @param <K>
   * @param <V>
   */
  private static final class 
  LRUHashMap<K, V> extends LinkedHashMap<K, V> {
    /**
     * SerialVersionUID.
     */
    private static final long serialVersionUID = 1L;

    /**
     * Cache size.
     */
    private final int fLimit;
    
    /**
     * Constructor.
     * @param limit Cache size.
     */
    public LRUHashMap(final int limit) {
      // Create access-ordered map.
      super(limit, LOAD_FACTOR, true);
      fLimit = limit;
    }
    
    /**
     * This method is called after a new element has been added to the map.
     * If it returns true, eldest element in the map is removed after
     * insertion (this is the least recently accessed element, becuase
     * the map is access-ordered).
     * @param eldest Element to be removed.
     * @return True iff element should be removed.
     */
    @Override
    protected boolean removeEldestEntry(final Map.Entry<K, V> eldest) {
      return size() > fLimit;
    }
  }    
  
  /**
   * Create cache with given size.
   * @param size Maximum number of objects in the cache.
   */
  public LRUCache(final int size) {
    fSize = size;
    fMap  = new LRUHashMap<String, C>(fSize);
  }
  
  /**
   * Add new object to cache or update existing binding.
   * If cache limit is exceeded, least recently used 
   * object is removed.
   * @param key Key.
   * @param object Object to be stored.
   */
  public void update(final String key, final C object) {
    if ((key == null) || (object == null)) {
      throw new NullPointerException();
    }
    fMap.put(key, object);
  }
  
  /**
   * Remove binding for given key from cache (if present).
   * @param key Key. Does not have to be bound.
   */
  public void remove(final String key) {
    fMap.remove(key);
  }
  
  /**
   * Retrieve object from cache. Return null if there is no
   * binding for the requested key.
   * @param key Key.
   * @return Retrieved value or {@code null} (if the key
   * is not bound in cache).
   */
  public C lookup(final String key) {
    return fMap.get(key);
  }
  
  /**
   * Check if there is a binding for given key in this LRUCache.
   * @param key Key
   * @return {@code true} iff key is bound in the cache.
   */
  public boolean hasKey(final String key) {
    // fMap.containsKey() does not update access time.
    return fMap.get(key) != null;
  }

  /**
   * Get number of objects in the cache.
   * @return cache size.
   */
  public int size() {
    return fMap.size();
  }
}
