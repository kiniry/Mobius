package mobius.directVCGen.formula;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.util.Repository;

import mobius.directVCGen.vcgen.ABasicVisitor;
import javafe.ast.ASTNode;
import javafe.ast.ConstructorDecl;
import javafe.ast.MethodDecl;
import javafe.ast.RoutineDecl;
import javafe.ast.TypeDecl;
import javafe.tc.TypeSig;
import javafe.tc.Types;

/**
 * This class is made to put into relation 
 * ESC/Java version and  BCEL version of a method.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class MethodGetter  {
  private static Repository fRepos;
  
  private static class Visitor extends ABasicVisitor {
    /** the currently treated method. */
    private final Method fMet;
    
    /**
     * Creates the visitor, which will look for the given method.
     * @param met the method to look for
     */
    private Visitor(final Method met) {
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
  }
  
  
  /**
   * Returns the ESC/Java method which corresponds to the given BCEL method.
   * @param sig the ESC/Java type where to find the method
   * @param met the method to look for
   * @return the ESC/Java routine declaration
   */
  public static RoutineDecl get(final TypeSig sig, final Method met) {
    final RoutineDecl rout = (RoutineDecl) sig.getCompilationUnit()
                                  .accept(new MethodGetter.Visitor(met), null); 
    if (rout == null) {
      throw new NullPointerException("" + met + sig.getCompilationUnit());
    }
    return rout;
  }

  public static void initTranslation(Repository repo) {
    fRepos = repo;
    //System.out.println("Repos set");
  }
  
  public static ClassGen translate(final TypeDecl td) {
    final String clss = td.id + "";
    JavaClass jc;
    try {
      jc = fRepos.loadClass(clss);
    } 
    catch (ClassNotFoundException e) {
      return null;
    }
    final ClassGen cg = new ClassGen(jc);
    return cg;
  }
  
  public static MethodGen translate(RoutineDecl rd) {
    final ClassGen cg = translate(rd.parent);
    
    String mt = "" + rd.id();
    if (mt.equals(cg.getJavaClass().getClassName())) {
      mt = "<init>";
    }
    final Method [] meths = cg.getMethods();
    MethodGen res = null;
    //System.out.println(mt);
    for (Method met: meths) {
      if (met.getName().equals(mt)) {
        res = new MethodGen(met, cg.getClassName(), cg.getConstantPool());
      }
    }
    return res;
  }
 
}
