package freeboogie.util;

import freeboogie.ast.AssociativeOperator;

public class PairAssocOp<U, V> implements AssociativeOperator<Pair<U,V>>{
  private final AssociativeOperator<U> uop;
  private final AssociativeOperator<V> vop;

  public PairAssocOp(AssociativeOperator<U> uop, AssociativeOperator<V> vop) {
    this.uop = uop;
    this.vop = vop;
  }

  @Override public Pair<U,V> zero() { 
    return Pair.of(uop.zero(), vop.zero()); 
  }

  @Override public Pair<U, V> plus(Pair<U, V> a, Pair<U, V> b) {
    return Pair.of(uop.plus(a.first, b.first), vop.plus(a.second, b.second));
  }
}
