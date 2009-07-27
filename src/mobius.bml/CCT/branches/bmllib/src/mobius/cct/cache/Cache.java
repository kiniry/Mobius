package mobius.cct.cache;

/**
 * Cache stores objects indexed by string keys.
 * It is similar to dictionary, but updates may delete
 * objects to save memory. 
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <C> Type of cached objects.
 */
public interface Cache<C> {
  /**
   * Add new object to cache or update existing binding.
   * @param key Key (must not be {@code null}).
   * @param object Object to be stored. Cannot be {@code null}.
   */
  void update(String key, C object);
  
  /**
   * Remove binding for given key from cache (if present).
   * @param key Key. Does not have to be bound.
   */
  void remove(String key);
  
  /**
   * Retrieve object from cache.
   * @param key Key.
   * @return Retrieved value or {@code null} (if the key
   * is not bound in cache).
   */
  C lookup(String key);
  
  /**
   * Check if there is a binding for given key in the cache.
   * @param key Key.
   * @return {@code true} iff key is bound in the cache.
   */
  boolean hasKey(String key);
  
  /**
   * Get number of objects in the cache.
   * @return cache size.
   */
  int size();
}
