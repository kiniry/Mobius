package freeboogie.backend;

import java.util.ArrayList;
import java.util.Arrays;

/**
 * S-expressions.
 *
 * TODO Add hash-consing and see the performance difference.
 *
 * @author rgrig 
 */
public class SmtTerm extends Term {
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
  
  /**
   * Creates a new term represented by an s-expression.
   * @param sort the sort of this term
   * @param id the identifier of this term
   * @param children the children of this term
   */
  public SmtTerm(Sort sort, String id, ArrayList<SmtTerm> children) {
    super(sort); 
    this.id = id;
    this.data = null;
    this.children = children;
//System.out.println("s.mk> " + id + " " + children.size());
    assert this.children.size() > 0;
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
