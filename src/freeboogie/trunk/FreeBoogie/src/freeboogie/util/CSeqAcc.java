package freeboogie.util;

import java.util.*;

import freeboogie.ast.AssociativeOperator;

/**
 * Used to accumulate multisets of things while evaluating the AST.
 * @param <E> the type of elements
 */
public class CSeqAcc<E> implements AssociativeOperator<CSeq<E>> {
  @Override public CSeq<E> zero() { return CSeq.mk(); }

  @Override public CSeq<E> plus(CSeq<E> a, CSeq<E> b) {
    return CSeq.mk(a, b);
  }
}
