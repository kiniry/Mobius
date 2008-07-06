package freeboogie.backend;

import java.util.Arrays;

/**
 * S-expressions.
 *
 * TODO Add hash-consing and see the performance difference.
 *      at the moment I think it will be slower (because I can't
 *      imagine anything that I plan doing generate a lot of
 *      duplicates)
 *
 * @author rgrig 
 */
public class SmtTerm extends Term {
  
  static final private SmtTerm[] noChild = new SmtTerm[0]; 
  
  /** The identifier or this term. */
  final public String id;
  
  /** 
   * If {@code id} says this term is a constant then {@code data}
   * contains the actual value of the constant (and {@code children}
   * is empty).
   */
  final public Object data;
  
  /** The children of this term, nonnull. */
  final public Term[] children;
  
  /**
   * Creates a new term represented by an s-expression.
   * @param sort the sort of this term
   * @param id the identifier of this term
   * @param children the children of this term
   */
  public SmtTerm(Sort sort, String id, Term[] children) {
    super(sort); 
    this.id = id;
    this.data = null;
    this.children = Arrays.copyOf(children, children.length);
    //System.out.println("mk> " + id + " " + children.length);
    assert this.children.length > 0;
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
    //System.out.println("mk2> " + id + " " + data);
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
    if (children != null) for (int i = 0; i < children.length; ++i) {
      if (i != 0) sb.append(" ");
      if (children[i] != null) sb.append(children[i].toString());
      else sb.append("null");
    }
    sb.append(")");
    return sb.toString();
  }
}
