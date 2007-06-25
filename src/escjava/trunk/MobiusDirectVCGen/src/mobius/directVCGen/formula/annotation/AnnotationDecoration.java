package mobius.directVCGen.formula.annotation;

import java.util.List;
import java.util.Vector;

import mobius.directVCGen.formula.Logic;

import escjava.sortedProver.Lifter.Term;

import javafe.ast.ASTDecoration;
import javafe.ast.ASTNode;

/**
 * This class is made to decorate the AST give by Javafe with the annotations
 * needed. 
 * @see ASTDecoration javafe.ast.ASTNode
 * @author J. Charles (julien.charles@inria.fr)
 */
public class AnnotationDecoration extends ASTDecoration {
  /** the current instance initialized of the annotation decorations. */
  public static final AnnotationDecoration inst = new AnnotationDecoration();

  /**
   * Constructor of the decoration helper.
   */
  public AnnotationDecoration() {
    super("annotationDecorations");
  }

  /**
   * A data structure to stock the informations inside the AST.
   * @author J. Charles
   */
  private static class Annotation {
    /** the pre annotations of the decorated instruction. */
    final List<AAnnotation> fPre = new Vector<AAnnotation>();
    /** the post annotations of the decorated instruction. */
    final List<AAnnotation> fPost = new Vector<AAnnotation>();
    /** the invariant associated with a while instruction. */
    Term fInv;
  }

  /**
   * Retrieve the annotation preceding the instruction.
   * @param n the node to retrieve the annotation from
   * @return an annotation or <code>null</code> if the 
   * node has not been decorated
   */
  public List<AAnnotation> getAnnotPre(final ASTNode n) {
    final Annotation v = getAnnot(n);
    if (v == null) {
      return null;
    }
    else {
      return v.fPre;
    }
  }

  /**
   * Retrieve the annotation being after the given instruction.
   * @param node the node from which to fetch the annotation
   * @return an annotation or <code>null</code> if the node 
   * has not been decorated
   */
  public List<AAnnotation> getAnnotPost(final ASTNode node) {
    final Annotation v = getAnnot(node);
    if (v == null) {
      return null;
    }
    else  {
      return v.fPost;
    }
  }

  /**
   * Retrieve the decoration of a given node.
   * @param n the node from which to retrieve the decoration
   * @return the decoration object
   */
  @SuppressWarnings("unchecked")
  private Annotation getAnnot(final ASTNode n) {
    final Annotation v = (Annotation) super.get(n);
    return v;
  }

  /**
   * Sets the annotation preceding the node.
   * @param n the node to decorate
   * @param v the annotation to set
   */
  public void setAnnotPre(final ASTNode n, final List<AAnnotation> v) {
    Annotation res = getAnnot(n);
    if (res == null) {
      res = new Annotation();
      super.set(n, res);
    }
    res.fPre.clear();
    res.fPre.addAll(v);
  }

  /**
   * Sets the annotation which is after the node.
   * @param n the node to decorate
   * @param v the annotation to set
   */
  public void setAnnotPost(final ASTNode n, final List<AAnnotation> v) {
    Annotation res = getAnnot(n);
    if (res == null) {
      res = new Annotation();
      super.set(n, res);
    }
    res.fPost.clear();
    res.fPost.addAll(v);
  }

  /**
   * Sets the invariant associated with the given node.
   * @param n the node to decorate
   * @param inv the invariant to set
   */
  public void setInvariant(final ASTNode n, final Term inv) {
    Annotation res = getAnnot(n);
    if (res == null) {
      res = new Annotation();
      super.set(n, res);
    }
    res.fInv = inv;
  }

  /**
   * Retrieve the invariant associated with the node.
   * @param n the node to decorate
   * @return the invariant the node is decorated with, or true
   */
  @SuppressWarnings("unchecked")
  public Term getInvariant(final ASTNode n) {
    final Annotation v =  getAnnot(n);
    if (v == null) {
      return null;
    }
    return v.fInv;
  }
}
