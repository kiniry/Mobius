package mobius.directVCGen.formula.annotation;

import java.util.List;
import java.util.Vector;

import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LineNumberGen;
import org.apache.bcel.generic.MethodGen;

import javafe.ast.ASTNode;
import javafe.ast.Stmt;
import javafe.util.Location;
import mobius.directVCGen.formula.ADecoration;
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
public class AnnotationDecoration extends ADecoration {
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
   * @param met the current method where the node is located
   * @param n the node to retrieve the annotation from
   * @return an annotation or <code>null</code> if the 
   * node has not been decorated or there is no pre annotation
   *  associated
   */
  public List<AAnnotation> getAnnotPre(final MethodGen met, 
                                       final ASTNode n) {

    return getAnnotPre(mkPositionHint(met, n));
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
   * @param prop informations about the variables which have to be 
   * added when the annotation is used
   */
  public void setInvariant(final PositionHint n, final Term inv, final ILocalVars prop) {
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
   * @param met the method which contains the node
   * @param n the node decorated
   * @return the invariant the node is decorated with, or null
   */
  public AAnnotation getInvariant(final MethodGen met,
                                  final ASTNode n) {
    return getInvariant(mkInvariantPositionHint(met, n));
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

  /**
   * Used to return the decoration of the given node from the given method.
   * @param met the method originating the node
   * @param x  the node to get the decoration from
   * @return the list of annotations being the decoration of the node
   */
  public List<AAnnotation> getAnnotPost(final MethodGen met, final ASTNode x) {
    return  getAnnotPost(mkPositionHint(met, x));
  }

  /**
   * Annotate a node with the given list of annotations.
   * @param met the method in which the node is located
   * @param s the node to annotate
   * @param annos the list of annotation
   */
  public void setAnnotPre(final MethodGen met, final Stmt s, final List<AAnnotation> annos) {
    setAnnotPre(mkPositionHint(met, s), annos);
    
  }

  /**
   * Decorate a node with an invariant.
   * @param met the method in which the node is located
   * @param s the node that has to be decorated with the invariant
   * @param inv the invariant
   * @param prop the local variables which are parameters to the invariant
   */
  public void setInvariant(final MethodGen met, final Stmt s, 
                           final Term inv, final ILocalVars prop) {

    setInvariant(mkInvariantPositionHint(met, s), inv, prop);
  }
  
  /**
   * Build a new position hint for invariants.
   * The position which is annotated is the last instruction of the
   * body of the loop.
   * 
   * @param met the method containing this annotation
   * @param s the loop instruction annotated
   * @return the position of the annotation inside of the loop
   */
  public static PositionHint mkInvariantPositionHint(final MethodGen met, final ASTNode s) {
    final int lineNum = Location.toLineNumber(s.getStartLoc());
    final List<LineNumberGen> lineList = Util.getLineNumbers(met, lineNum);
    final InstructionHandle last = Util.findLastInstruction(lineList);
    return new PositionHint(met, last);
  }
 
  /**
   * Build a new position hint for annotations.
   * The hypothesis taken into account is that the annotation
   * either ends a line or is on a new line; so the node is corresponds
   * to the first instruction on the following line.
   * 
   * @param met the method containing this annotation
   * @param n the instruction annotated
   * @return the position of the annotation
   */
  public static PositionHint mkPositionHint(final MethodGen met, final ASTNode n) {
    final int lineNum = Location.toLineNumber(n.getStartLoc());
    final List<LineNumberGen> lines = Util.getLineNumbers(met, lineNum);
    return new PositionHint(met, lines.get(0).getInstruction());
  }

}
