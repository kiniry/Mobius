package mobius.directVCGen.bico;

import org.apache.bcel.util.Repository;
import org.apache.bcel.generic.ClassGen;

public interface IAnnotationGenerator {
  /**
   * Annotates the given class by filling the Lookup structure
   * and using the annotation decorator. 
   * Returns false in case of problem.
   * @param clzz the class to annotate
   * @return
   */
  public boolean annotateClass(final Repository repos, 
                               final ClassGen clzz);
}
