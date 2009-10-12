package ie.ucd.bon.typechecker;

import ie.ucd.bon.util.KeyPair;

import java.util.Collection;
import java.util.HashMap;

import com.google.common.collect.LinkedHashMultimap;
import com.google.common.collect.Multimap;

public class TwoDimensionalMap<A,B,C> extends HashMap<KeyPair<A,B>,C> {

  private static final long serialVersionUID = 8052860720948202726L;

  private final Multimap<A,C> map;

  public TwoDimensionalMap() {
    map = LinkedHashMultimap.create();
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
    return super.put(key, value);
  }

  public Collection<C> getAll(A a) {
    return map.get(a);
  }

}
