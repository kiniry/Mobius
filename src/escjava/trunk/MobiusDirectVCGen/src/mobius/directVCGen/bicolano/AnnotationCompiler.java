package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.IOException;

import javafe.tc.TypeSig;

import mobius.bico.Executor;


/**
 * This class is made to compile the FOL formulas to Coq and 
 * attach them to the bytecode.
 * First it calls bico and compile the source to Coq.
 * Then it generates the annotations at the right program points.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class AnnotationCompiler {
  /** an instance of the class executor, the main class from bico. */
  private final Executor fExecutor;
  /**
   * Initialized the annotation compiler with the given arguments.
   * @param pkgsdir the directory where to generate the file(s) 
   * @param clzz the class to treat
   * @param sig the tree containing the annotations
   */
  public AnnotationCompiler(final File pkgsdir, final String clzz, TypeSig sig) {
    final String [] args = {pkgsdir.toString() + File.separator + 
                            "Bico", clzz};
    fExecutor = new Executor(args);
    
      
    
  }

  /**
   * Start the generation of the bicolano compatible file as
   * well as the generation of annotations.
   * @see Executor#start()
   * @throws IOException in case of I/O error
   * @throws ClassNotFoundException this exception can be launched by bico
   */
  public void start() throws IOException, ClassNotFoundException {
    fExecutor.start();
  }

}
