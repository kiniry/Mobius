package mobius.bico.dico;

import mobius.bico.dico.ClassConstants.Clss;
import mobius.bico.dico.ClassConstants.Meth;
import mobius.bico.dico.ClassConstants.Pkg;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.util.Repository;
import org.apache.bcel.util.SyntheticRepository;

/**
 * A class containing some utilities for the dictionnary.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class Dico {
  
  /**
   * Does nothing.
   */
  private Dico() {
    
  }
  /**
   * Initialize a dictionary with some standard values.
   * @param dico the dictionary to initialize
   * @throws ClassNotFoundException if the loading of the basic classes fails
   */
  public static void initDico(final ADictionary dico) throws ClassNotFoundException {
    final Repository repos = SyntheticRepository.getInstance();
    final JavaClass obj = repos.loadClass("java.lang.Object");
    final JavaClass thrw = repos.loadClass("java.lang.Throwable");
    final JavaClass excp = repos.loadClass("java.lang.Exception");
    final JavaClass str = repos.loadClass("java.lang.String");
    final JavaClass nllexcp = repos.loadClass("java.lang.NullPointerException");
    
    dico.addPackage(obj.getPackageName(), Pkg.JavaLang);
    dico.addPackage("", Pkg.Empty);
        
    dico.addClass(obj, Clss.object);
    dico.addClass(thrw, Clss.throwable);
    dico.addClass(excp, Clss.exception);
    dico.addClass(nllexcp, Clss.nullPointerException);
    dico.addClass(str, Clss.string);
    
    dico.addMethod(Meth.Obj, Pkg.JavaLang, Clss.object);
    dico.addMethod(Meth.Excp, Pkg.JavaLang, Clss.exception);
    dico.addMethod(Meth.NullExcp, Pkg.JavaLang, Clss.nullPointerException);
    dico.addMethod(Meth.Str, Pkg.JavaLang, Clss.string);
    dico.addMethod(Meth.Thrw, Pkg.JavaLang, Clss.throwable);
    // TODO complete the list...
  }
}
