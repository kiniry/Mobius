package mobius.directVCGen.formula.annotation;

import java.util.List;
import java.util.Vector;

import org.apache.bcel.generic.MethodGen;

import javafe.ast.ASTNode;
import javafe.ast.Stmt;
import mobius.directVCGen.formula.Decoration;
import mobius.directVCGen.formula.ILocalVars;
import mobius.directVCGen.formula.PositionHint;
import mobius.directVCGen.formula.Util;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

/**
 * This class is made to decorate the AST give by Javafe with the annotations
 * needed. 
 * @see ASTDecoration javafe.ast.ASTNode
 * @author J. Charles (julien.charles@inria.fr)
 */
public class AnnotationDecoration extends Decoration {
  /** the current instance initialized of the annotation decorations. */
  public static final AnnotationDecoration inst = new AnnotationDecoration();
  
  /** the number of invariants already generated for this method. */
  private int fInvCount;

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
    AAnnotation fInv;
    

  }

  /**
   * Retrieve the annotation preceding the instruction.
   * @param n the node to retrieve the annotation from
   * @return an annotation or <code>null</code> if the 
   * node has not been decorated or there is no pre annotation
   *  associated
   */
  public List<AAnnotation> getAnnotPre(final PositionHint n) {
    final Annotation v = getAnnot(n);
    List<AAnnotation> res;
    if (v == null) {
      res = null;
    }
    else if (v.fPre.size() < 1) {
      res = null;
    }
    else {
      res = v.fPre;
    }
    return res;
  }
  
  /**
   * Retrieve the annotation preceding the instruction.
   * @param n the node to retrieve the annotation from
   * @return an annotation or <code>null</code> if the 
   * node has not been decorated or there is no pre annotation
   *  associated
   */
  public List<AAnnotation> getAnnotPre(final MethodGen met, 
                                       final ASTNode n) {

    return getAnnotPre(new PositionHint(met, n));
  }


  /**
   * Retrieve the annotation being after the given instruction.
   * @param node the node from which to fetch the annotation
   * @return an annotation or <code>null</code> if the node 
   * has not been decorated or there is no post annotation
   *  associated
   */
  public List<AAnnotation> getAnnotPost(final PositionHint node) {
    final Annotation v = getAnnot(node);
    List<AAnnotation> res;
    if (v == null) {
      res = null;
    }
    else if (v.fPost.size() < 1) {
      res = null;
    }
    else {
      res = v.fPost;
    }
    return res;

  }

  /**
   * Retrieve the decoration of a given node.
   * @param n the node from which to retrieve the decoration
   * @return the decoration object
   */
  private Annotation getAnnot(final PositionHint n) {
    final Annotation v = (Annotation) super.get(n);
    return v;
  }

  /**
   * Sets the annotation preceding the node.
   * @param n the node to decorate
   * @param v the annotation to set
   */
  public void setAnnotPre(final PositionHint n, final List<AAnnotation> v) {
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
  public void setAnnotPost(final PositionHint n, final List<AAnnotation> v) {
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
   * @param prop the properties to add all the arguments to the invariant
   */
  public void setInvariant(final PositionHint n, final Term inv, ILocalVars prop) {
    Annotation res = getAnnot(n);
    if (res == null) {
      res = new Annotation();
      super.set(n, res);
    }
    res.fInv = new Assert("invariant" + fInvCount,
                          Util.buildArgs(prop),
                          inv);

    fInvCount++;
    
    
  }
  

  /**
   * Retrieve the invariant associated with the node.
   * @param n the node decorated
   * @return the invariant the node is decorated with, or null
   */
  public AAnnotation getInvariant(final PositionHint n) {
    final Annotation v =  getAnnot(n);
    if (v == null) {
      return null;
    }
    return v.fInv;
  }
  
  /**
   * Retrieve the invariant associated with the node.
   * @param n the node decorated
   * @return the invariant the node is decorated with, or null
   */
  public AAnnotation getInvariant(final MethodGen met,
                                  final ASTNode n) {
    return getInvariant(new PositionHint(met, n));
  }
  
  /**
   * Retrieve the invariant name associated with the node.
   * @param n the node decorated
   * @return the invariant name  the node is decorated with, or null
   */
  public String getInvariantName(final PositionHint n) {
    final Annotation v =  getAnnot(n);
    if (v == null) {
      return null;
    }
    return v.fInv.getName();
  }

  /**
   * Returns the arguments (a variable list) associated with the invariant,
   * if the node is decorated with an invariant. Returns <code>null</code>
   * otherwise.
   * @param x the node that contains the invariant
   * @return a variable list that are the arguments of the invariant
   */
  public List<QuantVariableRef> getInvariantArgs(final PositionHint x) {
    final Annotation v =  getAnnot(x);
    if (v == null) {
      return null;
    }
    return v.fInv.getArgs();
  }

  public List<AAnnotation> getAnnotPost(MethodGen met, ASTNode x) {
    return  getAnnotPost(new PositionHint(met, x));
  }

  public void setAnnotPre(MethodGen met, Stmt s, List<AAnnotation> annos) {
    setAnnotPre(new PositionHint(met, s), annos);
    
  }

  public void setInvariant(MethodGen met, Stmt s, Term inv, ILocalVars prop) {
    setInvariant(new PositionHint(met, s), inv, prop);
  }
}
