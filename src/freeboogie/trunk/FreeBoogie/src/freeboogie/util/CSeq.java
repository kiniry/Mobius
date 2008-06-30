package freeboogie.util;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Iterator;

/**
 * A persistent sequence with fast concatenation and iteration.
 */
public class CSeq<E> implements Iterable<E> {
  static private class Concat<E> extends CSeq<E> { 
    private CSeq<E> left, right;
    public Concat(CSeq<E> left, CSeq<E> right) {
      this.left = left;
      this.right = right;
    }
  }
  static private class One<E> extends CSeq<E> {
    private E data;
    public One(E data) { this.data = data; }
  }
  static private class Empty<E> extends CSeq<E> {}

  static public <E> CSeq<E> mk() { return new Empty<E>(); }
  static public <E> CSeq<E> mk(E e) { return new One<E>(e); }
  static public <E> CSeq<E> mk(CSeq<E> a, CSeq<E> b) {
    if (a instanceof Empty) return b;
    if (b instanceof Empty) return a;
    return new Concat<E>(a, b);
  }

  class It<E> implements Iterator<E> {
    Deque<CSeq<E>> pos = new ArrayDeque<CSeq<E>>();

    @Override public boolean hasNext() { return !pos.isEmpty(); }

    @Override public E next() {
      CSeq<E> p, c = pos.removeFirst();
      E r = ((One<E>)c).data;
      while ((p = pos.pollFirst()) != null && ((Concat<E>)p).right == c) c = p;
      if (p != null) {
        pos.addFirst(p); p = ((Concat<E>)p).right;
        while (true) {
          pos.addFirst(p);
          if (!(p instanceof Concat)) break;
          p = ((Concat<E>)p).left;
        }
      }
      return r;
    }

    @Override public void remove() throws UnsupportedOperationException {
      throw new UnsupportedOperationException("CSeq is immutable.");
    }
  }

  @Override public Iterator<E> iterator() {
    It<E> r = new It<E>();
    if (this instanceof Empty) return r;
    CSeq<E> p = this;
    while (true) {
      r.pos.addFirst(p);
      if (!(p instanceof Concat)) break;
      p = ((Concat<E>)p).left;
    }
    return r;
  }

  // === small tests ===
  public static void main(String args[]) {
    CSeq<Integer> empty = CSeq.mk();
    System.out.println("=== empty:");
    for (Integer x : empty) System.out.println(x);

    CSeq<Integer> one = CSeq.mk(1);
    System.out.println("=== 1:");
    for (Integer x : one) System.out.println(x);

    CSeq<Integer> bigger = CSeq.mk(
      CSeq.mk(
        one,
        CSeq.mk(2)),
      CSeq.mk(
        CSeq.mk(2),
        one));
    System.out.println("=== 1,2,2,1:");
    for (Integer x : bigger) System.out.println(x);

    System.out.println("=== 1:");
    for (Integer x : one) System.out.println(x);
  }
}

