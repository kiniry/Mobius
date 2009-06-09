package ie.ucd.bon.typechecker;

import ie.ucd.bon.util.KeyPair;

import java.util.HashMap;

public class TwoDimensionalMap<A,B,C> extends HashMap<KeyPair<A,B>,C> {

  private static final long serialVersionUID = 8052860720948202726L;

  public C get(A a, B b) {
    return super.get(new KeyPair<A,B>(a,b));
  }

  public C put(A a, B b, C value) {
    return super.put(new KeyPair<A,B>(a,b), value);
  }

  
  
}
