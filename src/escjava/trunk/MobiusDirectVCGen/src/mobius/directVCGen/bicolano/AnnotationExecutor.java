package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.FileNotFoundException;

import org.apache.bcel.generic.ClassGen;

import mobius.bico.ClassExecutor;
import mobius.bico.Executor;

/**
 * An executor that generates the annotations for the class
 * as well.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class AnnotationExecutor extends Executor {
  /** the current working directory. */
  private final File fWorkingDir;


  
  public AnnotationExecutor(File workingDir, String [] args) {
    super(args);
    fWorkingDir = workingDir; 
  }

  
  /**
   * Returns an instance of a class executor.
   * This method is there as an extension point.
   * @param cg the class generator. Represents the current class
   * to treat.
   * @return a ClassExecutor instance
   * @throws FileNotFoundException if a file is missing
   */
  public ClassExecutor getClassExecutor(final ClassGen cg) throws FileNotFoundException {
    return new AnnotationClassExecutor(this, cg, fWorkingDir);
  }
}
