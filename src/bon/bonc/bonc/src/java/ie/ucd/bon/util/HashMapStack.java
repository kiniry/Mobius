/**
 * Copyright (c) 2007-2010, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class HashMapStack<K,V> implements Map<K, V> {

  private final LinkedList<Map<K,V>> stack;
  
  public HashMapStack() {
    stack = new LinkedList<Map<K,V>>();
    clear();
  }
   
  public void push() {
    stack.addFirst(new HashMap<K,V>());
  }
  
  public void pop() {
    if (stack.size() > 0) {
      stack.removeFirst();
    }
  }


  @Override
  public void clear() {
    stack.clear();
    stack.add(new HashMap<K,V>());
  }


  @Override
  public boolean containsKey(Object key) {
    for (Map<K,V> map : stack) {
      if (map.containsKey(key)) {
        return true;
      }
    }
    return false;
  }


  @Override
  public boolean containsValue(Object value) {
    for (Map<K,V> map : stack) {
      if (map.containsValue(value)) {
        return true;
      }
    }
    return false;
  }


  @Override
  public Set<Entry<K, V>> entrySet() {
    Set<Entry<K,V>> allEntries = new HashSet<Entry<K,V>>();
    for (Map<K,V> map : stack) {
      allEntries.addAll(map.entrySet());
    }
    return allEntries;
  }


  @Override
  public V get(Object key) {
    for (Map<K,V> map : stack) {
      V value = map.get(key);
      if (value != null) {
        return value;
      }
    }
    return null;
  }


  @Override
  public boolean isEmpty() {
    for (Map<K,V> map : stack) {
      if (!map.isEmpty()) {
        return false;
      }
    }
    return true;
  }


  @Override
  public Set<K> keySet() {
    Set<K> allKeys = new HashSet<K>();
    for (Map<K,V> map : stack) {
      allKeys.addAll(map.keySet());
    }
    return allKeys;
  }


  @Override
  public V put(K key, V value) {
    return stack.getFirst().put(key, value);
  }


  @Override
  public void putAll(Map<? extends K, ? extends V> m) {
    stack.getFirst().putAll(m);
  }


  @Override
  public V remove(Object key) {
    for (Map<K,V> map : stack) {
      V value = map.get(key);
      if (value != null) {
        map.remove(key);
        return value;
      }
    }
    return null;
  }


  @Override
  public int size() {
    // Sum individual sizes
    int count = 0;
    for (Map<K,V> map : stack) {
      count += map.size();
    }
    return count;
  }


  @Override
  public Collection<V> values() {
    List<V> allValues = new ArrayList<V>(size());
    for (Map<K,V> map : stack) {
      allValues.addAll(map.values());
    }
    return allValues;
  }
  
  
  
}
