package mobius.directVCGen.bico;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import mobius.bico.executors.Executor;


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
   * @param classpath the current classpath used by to find the source files
   * @param generator the annotation generator used to decorate the AST.
   */
  public AnnotationCompiler(final File pkgsdir, final String clzz,
                            final String classpath,
                            final IAnnotationGenerator generator) {
    final List<String> classes = new ArrayList<String>();
    classes.add(clzz);
    String cp = classpath;
    if (cp == null) {
      cp = "";
    }
    fExecutor = new AnnotationExecutor(pkgsdir, cp, classes, generator);
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
