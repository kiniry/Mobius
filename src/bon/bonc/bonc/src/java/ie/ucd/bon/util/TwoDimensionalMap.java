/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.util;


import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Multimap;

public class TwoDimensionalMap<A,B,C> extends HashMap<KeyPair<A,B>,C> {

  private static final long serialVersionUID = 8052860720948202726L;

  private final Multimap<A,C> map;
  private final Multimap<C,A> reverseMap;
  
  private final Multimap<A,KeyPair<B,C>> firstDimensionMap;
  
  private final Map<A,Map<B,C>> secondDimensionMap;

  public TwoDimensionalMap() {
    map = LinkedHashMultimap.create();
    reverseMap = LinkedHashMultimap.create();
    firstDimensionMap = LinkedHashMultimap.create();
    secondDimensionMap = new HashMap<A,Map<B,C>>();
  }

  public C get(A a, B b) {
    return get(new KeyPair<A,B>(a,b));
  }

  public C put(A a, B b, C value) {
    return put(new KeyPair<A,B>(a,b), value);
  }

  @Override
  public C put(KeyPair<A, B> key, C value) {
    map.put(key.a, value);
    reverseMap.put(value, key.a);
    firstDimensionMap.put(key.a, new KeyPair<B,C>(key.b,value));
    
    Map<B,C> second = secondDimensionMap.get(key.a);
    if (second == null) {
      second = new HashMap<B,C>();
      secondDimensionMap.put(key.a, second);
    }
    second.put(key.b, value);
    
    return super.put(key, value);
  }

  @Override
  /**
   * Do not use, not supported and will throw an exception.
   */
  public C remove(Object key) {
    throw new UnsupportedOperationException();
  }

  public Collection<C> getAll(A a) {
    return map.get(a);
  }
  
  public Collection<KeyPair<B,C>> getAllPairs(A a) {
    return firstDimensionMap.get(a);
  }
  
  public Collection<A> getMappedFrom(C c) {
    return reverseMap.get(c);
  }

  public boolean containsKey(A a, B b) {
    return containsKey(new KeyPair<A,B>(a,b));
  }
  
  public Map<B,C> getSecondDimension(A a) {
    Map<B,C> second = secondDimensionMap.get(a);
    return second == null ? ImmutableMap.<B,C>of() : second;
  }

}
