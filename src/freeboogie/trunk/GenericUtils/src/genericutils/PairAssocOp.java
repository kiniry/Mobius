package genericutils;

/**
 * A pair of associative operators.
 * @param <U> the type of the first elements in pairs
 * @param <V> the type of the second element in pairs
 */
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
