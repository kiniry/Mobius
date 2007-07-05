package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.FileNotFoundException;

import javafe.tc.TypeSig;

import org.apache.bcel.generic.ClassGen;

import mobius.bico.executors.ClassExecutor;
import mobius.bico.executors.Executor;

/**
 * An executor that generates the annotations for the class
 * as well.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class AnnotationExecutor extends Executor {
  /** the current working directory. */
  private final File fWorkingDir;
  /** the type sygnature of the currently handled class. */
  private final TypeSig fSig;

  
  /**
   * Create the special annotation executor.
   * @param workingDir the directory where to generate the files
   * @param sig the type signature which expresses the program
   * to treat
   * @param args the 'normal' arguments that should be given
   * to bico
   */
  public AnnotationExecutor(final File workingDir, final TypeSig sig, 
                            final String [] args) {
    super(args);
    fWorkingDir = workingDir; 
    fSig = sig;
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
    return new AnnotationClassExecutor(this, cg, fWorkingDir, fSig, this.getModuleName());
  }



}
