package mobius.directvcgen.bico;

import java.util.List;

import org.apache.bcel.util.Repository;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.MethodGen;

/**
 * The interface used to represent the generator of annotations.
 * The generator use the AnnotationDecorations to decorate the file.
 * It also fills the Lookup utility object.
 * @see mobius.directvcgen.formula.annotation.AnnotationDecoration
 * @see mobius.directvcgen.formula.Lookup
 * @author J. Charles (julien.charles@inria.fr)
 */
public interface IAnnotationGenerator {
  /**
   * Annotates the given class by filling the Lookup structure
   * and using the annotation decorator. 
   * Returns false in case of problem.
   * @param repos the repository which contains the classpath
   * @param clzz the class to annotate
   * @return a result, true if everything went well
   */
  boolean annotateClass(final Repository repos, 
                               final ClassGen clzz);
  
  /**
   * Returns the arguments name for a method, 
   * consistant with the annotations.
   * For JavaFE arguments, it does the following:
   * instead of having for a method the arguments [arg0, arg1, ...]
   * given by BCEL, it will return the arguments [x_12_23, y_13_23, ...].
   * 
   * @param mg the methods from which the arguments should be retrieved
   * @return a list of string eg. [x_1, y, a]
   */
  List<String> getArgumentsName(final MethodGen mg);
}
