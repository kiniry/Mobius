package mobius.directvcgen.translator;

import java.util.ArrayList;
import java.util.List;

import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.RoutineDecl;
import javafe.tc.TypeSig;
import mobius.directvcgen.bico.IAnnotationGenerator;
import mobius.directvcgen.formula.Translator;

import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.util.Repository;

import escjava.translate.UniqName;

/**
 * An annotation generator that can be used to convert the annotations
 * from the ESC Java/ JavaFE AST to first order logic formulas.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class JMLAnnotationGenerator implements IAnnotationGenerator {
  

  
  /** {@inheritDoc} */
  public boolean annotateClass(final Repository repo, final ClassGen clzz) {
    Translator.init(repo);
    final TypeSig sig = Translator.getInst().getSig(clzz.getJavaClass());
    sig.getCompilationUnit().accept(new JmlVisitor(false), null);
    return checkConsistency(clzz, sig);
  }


  
  /**
   * Check if the BCEL class is consistent with the ESC/Java2 signature.
   * @param clzz the BCEL version of the class
   * @param sig the ESC/Java2 signature
   * @return true if both fields have the same class name and package
   */
  private boolean checkConsistency(final ClassGen clzz, 
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

  /** {@inheritDoc} */

  public List<String> getArgumentsName(final MethodGen mg) {
    final RoutineDecl rd = Translator.getInst().get(mg);
    final List<String> v = new ArrayList<String>();
    final FormalParaDeclVec fpdvec = rd.args;
    
    final FormalParaDecl[] args = fpdvec.toArray();
    for (FormalParaDecl decl: args) {
      final String name = UniqName.variable(decl);
      v.add(name);
    }
    return v;
  }


}
