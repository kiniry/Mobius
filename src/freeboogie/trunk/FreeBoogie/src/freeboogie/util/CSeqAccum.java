package freeboogie.util;

import java.util.*;

import freeboogie.ast.AssociativeOperator;

public class CSeqAcc<E> implements AssociativeOperator<Set<E>> {
  @Override public TreeSet<E> zero() { return new TreeSet<E>(); }

  @Override public TreeSet<E> plus(Set<E> a, Set<E> b) {
    TreeSet<E> result = zero();
    result.addAll(a);
    result.addAll(b);
    return result;
  }
}
