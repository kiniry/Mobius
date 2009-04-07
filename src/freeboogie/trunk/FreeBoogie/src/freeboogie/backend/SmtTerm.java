package freeboogie.backend;

import java.util.*;

/**
 * S-expressions.
 *
 * TODO Add hash-consing and see the performance difference.
 *
 * @author rgrig 
 */
public final class SmtTerm extends Term<SmtTerm> {
  private static final ArrayList<SmtTerm> noChild = new ArrayList<SmtTerm>();
  
  private static final HashMap<SmtTerm, SmtTerm> cache =
    new HashMap<SmtTerm, SmtTerm>(100003);

  private int hash;

  /** The identifier or this term. */
  public final String id;
  
  /** 
   * If {@code id} says this term is a constant then {@code data}
   * contains the actual value of the constant (and {@code children}
   * is empty).
   */
  public final Object data;
  
  /** The children of this term, nonnull. */
  public final ArrayList<SmtTerm> children;

  private HashSet<SmtTerm> axioms;
  
  /**
   * Creates a new term represented by an s-expression.
   * @param sort the sort of this term
   * @param id the identifier of this term
   * @param children the children of this term
   */
  private SmtTerm(Sort sort, String id, ArrayList<SmtTerm> children) {
    super(sort); 
    assert children != null;
    this.id = id;
    this.data = null;
    this.children = children;
//System.out.println("s.mk> " + id + " " + children.size());
  }

  /** Creates a new constant. */
  private SmtTerm(Sort sort, String id, Object data) {
    super(sort); 
    this.id = id;
    this.data = data;
    this.children = noChild;
//System.out.println("s.mk2> " + id + " " + data);
  }

  public static SmtTerm mk(Sort sort, String id, ArrayList<SmtTerm> children) {
    return hashCons(new SmtTerm(sort, id, children));
  }

  public static SmtTerm mk(Sort sort, String id, Object data) {
    return hashCons(new SmtTerm(sort, id, data));
  }

  private static SmtTerm hashCons(SmtTerm n) {
    SmtTerm old = cache.get(n);
    if (old == null)
      cache.put(n, n);
    else
      n = old;
    return n;
  }

  @Override
  public boolean equals(Object o) {
    if (o == this) return true;
    if (!(o instanceof SmtTerm)) return false;
    SmtTerm t = (SmtTerm)o;
    if (!id.equals(t.id)) return false;
    if (data == null ^ t.data == null) return false;
    if (data != null && !data.equals(t.data)) return false;
    return children.equals(t.children);
  }

  @Override
  public int hashCode() {
    if (hash != 0) return hash;
    hash = id.hashCode();
    if (data != null) hash += data.hashCode();
    hash += children.hashCode();
    return hash;
  }

  @Override
  public void collectAxioms(Set<SmtTerm> axiomBag) {
    recCollectAxioms(axiomBag, new HashSet<SmtTerm>());
  }

  @Override
  public void addAxiom(SmtTerm t) {
    if (axioms == null) axioms = new HashSet<SmtTerm>();
    axioms.add(t);
  }

  /* For debug. */
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("(");
    sb.append(id);
    sb.append(" ");
    if (data != null) {
      sb.append("[");
      sb.append(data.toString());
      sb.append("]");
    }
    for (SmtTerm c : children) {
      sb.append(" ");
      sb.append(c.toString());
    }
    sb.append(")");
    return sb.toString();
  }

  private void recCollectAxioms(Set<SmtTerm> axiomBag, HashSet<SmtTerm> seen) {
    if (seen.contains(this)) return;
    seen.add(this);
    if (axioms != null) axiomBag.addAll(axioms);
    for (SmtTerm t : children) t.recCollectAxioms(axiomBag, seen);
  }
}
