/* A small program to check the timing for building up sets by
 * various methods. Example application: Collect all ids that appear
 * in various subexpressions and then iterate thru them.
 */

import java.util.*;

interface Tree { void print(); }
class InternalNode implements Tree {
  public Tree left;
  public Tree right;
  public InternalNode(Tree left, Tree right) {
    this.left = left;
    this.right = right;
  }
  public void print() { left.print(); right.print(); }
}
class ExternalNode implements Tree {
  public int data;
  public ExternalNode(int data) { this.data = data; }
  public void print() { System.err.println(data); }
}

public class TS {
  public static Set<Integer> mk(int l, int h) {
    TreeSet<Integer> result = new TreeSet<Integer>();
    if (h - l < 2) result.add(l);
    else {
      int m = (l + h) >>> 1;
      result.addAll(mk(l, m));
      result.addAll(mk(m, h));
    }
    return result;
  }

  public static Tree mk2(int l, int h) {
    if (h - l < 2) return new ExternalNode(l);
    int m = (l + h) >>> 1;
    return new InternalNode(mk2(l, m), mk2(m, h));
  }

  public static CSeq<Integer> mk3(int l, int h) {
    if (h - l < 2) return new CSeq.One<Integer>(l);
    int m = (l + h) >>> 1;
    return new CSeq.Concat<Integer>(mk3(l, m), mk3(m, h));
  }

  public static void main(String[] args) {
    int M;
    long start;
    for (M = 1; M > 0; M *= 10) {
      System.out.print("M="+M+"; ");

      start = System.currentTimeMillis();
      Tree all2 = mk2(0, M);
      System.out.print("ms2=" + (System.currentTimeMillis() - start)+"; ");
      all2.print();
      all2 = null; System.gc();

      start = System.currentTimeMillis();
      CSeq<Integer> all3 = mk3(0, M);
      System.out.print("ms3=" + (System.currentTimeMillis() - start)+"; ");
      for (Integer i : all3) System.err.println(i);
      all3 = null; System.gc();

      start = System.currentTimeMillis();
      Set<Integer> all = mk(0, M);
      System.out.print("ms="+(System.currentTimeMillis() - start)+"; ");
      for (Integer i : all) System.err.println(i);
      all = null; System.gc();

      System.out.println();
    }
  }
}
