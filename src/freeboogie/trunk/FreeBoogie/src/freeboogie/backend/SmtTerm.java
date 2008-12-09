package freeboogie.backend;

import java.util.*;

/**
 * S-expressions.
 *
 * TODO Add hash-consing and see the performance difference.
 *
 * @author rgrig 
 */
public class SmtTerm extends Term<SmtTerm> {
  static final private ArrayList<SmtTerm> noChild = new ArrayList<SmtTerm>();
  
  /** The identifier or this term. */
  final public String id;
  
  /** 
   * If {@code id} says this term is a constant then {@code data}
   * contains the actual value of the constant (and {@code children}
   * is empty).
   */
  final public Object data;
  
  /** The children of this term, nonnull. */
  final public ArrayList<SmtTerm> children;

  private HashSet<SmtTerm> axioms;
  
  /**
   * Creates a new term represented by an s-expression.
   * @param sort the sort of this term
   * @param id the identifier of this term
   * @param children the children of this term
   */
  public SmtTerm(Sort sort, String id, ArrayList<SmtTerm> children) {
    super(sort); 
    assert children != null;
    this.id = id;
    this.data = null;
    this.children = children;
//System.out.println("s.mk> " + id + " " + children.size());
  }

  /**
   * Creates a new constant.
   * @param sort the sort of this constant
   * @param id the identifier of this constant type
   * @param data the constant
   */
  public SmtTerm(Sort sort, String id, Object data) {
    super(sort); 
    this.id = id;
    this.data = data;
    this.children = noChild;
//System.out.println("s.mk2> " + id + " " + data);
  }

  @Override
  public boolean equals(Object o) {
    if (!(o instanceof SmtTerm)) return false;
    SmtTerm t = (SmtTerm)o;
    if (!id.equals(t.id)) return false;
    if (data == null ^ t.data == null) return false;
    if (data != null && !data.equals(t.data)) return false;
    return children.equals(t.children);
  }

  @Override
  public int hashCode() {
    int result = id.hashCode();
    if (data != null) result += data.hashCode();
    result += children.hashCode();
    return result;
  }

  @Override
  public void collectAxioms(Set<SmtTerm> axiomBag) {
    if (axioms != null) axiomBag.addAll(axioms);
    for (SmtTerm t : children) t.collectAxioms(axiomBag);
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
}
