package mobius.directVCGen.bicolano;

import org.apache.bcel.classfile.Method;

import mobius.directVCGen.vcgen.ABasicVisitor;
import javafe.ast.ASTNode;
import javafe.ast.ConstructorDecl;
import javafe.ast.MethodDecl;
import javafe.ast.RoutineDecl;
import javafe.tc.TypeSig;

/**
 * This class is made to return the ESC/Java version of a BCEL method
 * definition.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class MethodGetter extends ABasicVisitor {
    /** the currently treated method. */
  private final Method fMet;
  
  /**
   * Creates the visitor, which will look for the given method.
   * @param met the method to look for
   */
  private MethodGetter(final Method met) {
    fMet = met;
  }
  
  /** {@inheritDoc} */
  @Override
  public Object visitASTNode(final ASTNode x, final Object o) {
    Object res = o;
  
    final int max = x.childCount();
  
    for (int i = 0; i < max; i++) {
      final Object child = x.childAt(i);
      if (child instanceof ASTNode) {
        res = ((ASTNode) child).accept(this, res);
      }
    }
    return res;
  }
  /**
   * Method to visit a constructor and generate its annotations.
   * @param cd the constructor to visit
   * @param o the output String
   * @return an updated String with the annotations
   */
  @Override
  public Object visitConstructorDecl(final /*@non_null*/ ConstructorDecl cd, 
                                     final Object o) {
    if (fMet.getName().equals("<init>")) {
      return cd;
    }
    return o;
  }
  
  /**
   * Visits a method and generate its annotations.
   * @param md the method to visit
   * @param o the output String
   * @return an updated String with the annotations
   */
  @Override
  public Object visitMethodDecl(final /*@non_null*/ MethodDecl md, 
                                final Object o) {
    if (fMet.getName().equals(md.id().toString())) {
      return md;
    }
    return o;
    
  }
  
  /**
   * Returns the ESC/Java method which corresponds to the given BCEL method.
   * @param sig the ESC/Java type where to find the method
   * @param met the method to look for
   * @return the ESC/Java routine declaration
   */
  public static RoutineDecl get(final TypeSig sig, final Method met) {
    final RoutineDecl rout = (RoutineDecl) sig.getCompilationUnit()
                                  .accept(new MethodGetter(met), null); 
    if (rout == null) {
      throw new NullPointerException("" + met + sig.getCompilationUnit());
    }
    return rout;
  }
}
