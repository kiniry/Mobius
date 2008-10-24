package mobius.directVCGen.translator;

import javafe.tc.OutsideEnv;
import javafe.tc.TypeSig;

import mobius.directVCGen.bico.IAnnotationGenerator;
import mobius.directVCGen.formula.MethodGetter;

import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.util.Repository;

/**
 * An annotation generator that can be used to convert the annotations
 * from the ESC Java/ JavaFE AST to first order logic formulas.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class JMLAnnotationGenerator implements IAnnotationGenerator {
  
  /** {@inheritDoc} */
  public boolean annotateClass(final ClassGen clzz) {
    final Repository repo = clzz.getJavaClass().getRepository();
    MethodGetter.initTranslation(repo);
    
    
    String [] pkg =  clzz.getJavaClass().getPackageName().split("\\.");
    //System.out.println(pkg[0] + " " + pkg.length);
    if (pkg[0].equals("")) {
      pkg = new String[0];
    }
    final String [] n = clzz.getJavaClass().getClassName().split("\\.");
    //System.out.println(n[n.length - 1]);
    final TypeSig sig = OutsideEnv.lookup(pkg, n[n.length - 1]);
    sig.typecheck();
    sig.getCompilationUnit().accept(new JmlVisitor(false), null);
    return checkConsistency(clzz, sig);
  }
  
  /**
   * Check if the field {@link #fClass} is consistent with the field
   * {@link #fSig}.
   * @param clzz the BCEL version of the class
   * @param sig the ESCJava version of the class
   * @return true if both fields have the same class name and package
   */
  private static boolean checkConsistency(final ClassGen clzz,
                                   final TypeSig sig) {
    // building the full name from fSig: basically an array
    final String[] pk = sig.packageName;
    final String [] fullNameSig = new String[pk.length + 1];
    System.arraycopy(pk, 0, fullNameSig, 0, pk.length);
    fullNameSig[pk.length] = sig.simpleName;
    final String [] fullName = clzz.getClassName().split("\\.");
    
    // checking if both are equal
    if (fullName.length != fullNameSig.length) {
      return false;
    }
    for (int i = 0; i < fullName.length; i++) {
      if (!fullName[i].equals(fullNameSig[i])) {
        return false;
      }
    }
    return true;
  }
}
