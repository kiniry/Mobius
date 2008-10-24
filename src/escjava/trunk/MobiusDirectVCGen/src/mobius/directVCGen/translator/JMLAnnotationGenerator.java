package mobius.directVCGen.translator;

import javafe.tc.OutsideEnv;
import javafe.tc.TypeSig;

import mobius.directVCGen.bico.IAnnotationGenerator;

import org.apache.bcel.generic.ClassGen;

public class JMLAnnotationGenerator implements IAnnotationGenerator {

  /** the current class which is inspected. */
  private ClassGen fClass;
  /** the type sygnature of the currently handled class. */
  private TypeSig fSig;
  
  
  /** {@inheritDoc} */
  public boolean annotateClass(final ClassGen clzz) {
    fClass = clzz;
    String [] pkg = fClass.getJavaClass().getPackageName().split("\\.");
    //System.out.println(pkg[0] + " " + pkg.length);
    if (pkg[0].equals("")) {
      pkg = new String[0];
    }
    final String [] n = fClass.getJavaClass().getClassName().split("\\.");
    //System.out.println(n[n.length - 1]);
    fSig = OutsideEnv.lookup(pkg, n[n.length - 1]);
    fSig.typecheck();
    fSig.getCompilationUnit().accept(new JmlVisitor(false), null);
    return checkConsistency();
  }
  
  /**
   * Check if the field {@link #fClass} is consistent with the field
   * {@link #fSig}.
   * @return true if both fields have the same class name and package
   */
  private boolean checkConsistency() {
    // building the full name from fSig: basically an array
    final String[] pk = fSig.packageName;
    final String [] fullNameSig = new String[pk.length + 1];
    System.arraycopy(pk, 0, fullNameSig, 0, pk.length);
    fullNameSig[pk.length] = fSig.simpleName;
    final String [] fullName = fClass.getClassName().split("\\.");
    
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
