package mobius.bico.dico;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.util.Repository;
import org.apache.bcel.util.SyntheticRepository;

/**
 * A class containing some utilities for the dictionnary.
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class Dico implements IClassConstants {
  
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
  public static void initDico(final Dictionary dico) throws ClassNotFoundException {
    final Repository repos = SyntheticRepository.getInstance();
    final JavaClass obj = repos.loadClass("java.lang.Object");
    final JavaClass thrw = repos.loadClass("java.lang.Throwable");
    final JavaClass excp = repos.loadClass("java.lang.Exception");
    final JavaClass str = repos.loadClass("java.lang.String");
  
    
    dico.addPackage(obj.getPackageName(), pkgJavaLang);
    dico.addPackage("", pkgEmpty);
        
    dico.addClass(obj, object);
    dico.addClass(thrw, throwable);
    dico.addClass(excp, exception);
    dico.addClass(str, string);
    
    dico.addMethod("Object.<init>", pkgJavaLang, object, methObj);
    dico.addMethod("Exception.<init>", pkgJavaLang, exception, methExcp);
    dico.addMethod("String.<init>", pkgJavaLang, string, methStr);
    dico.addMethod("Throwable.<init>", pkgJavaLang, throwable, methThrw);
    // TODO complete the list...
  }
}
