package mobius.bico;

import java.io.File;
import java.io.IOException;

import mobius.bico.Util.Stream;
import mobius.bico.dico.Dictionary;
import mobius.bico.implem.IImplemSpecifics;

import org.apache.bcel.util.Repository;

/**
 * The generic executor class.
 * @author J. Charles (julien.charles@inria.fr), 
 * P. Czarnik (czarnik@mimuw.edu.pl), 
 * L. Hubert (laurent.hubert@irisa.fr)
 */
public abstract class ABasicExecutor {
  
  /** a data structure to stock methods signatures. */
  final MethodHandler fMethodHandler;

  /** the dictionnary to convert Coq's class numbers to human readable forms. */
  final Dictionary fDico;
  
  /** Bicolano's implementations specific handlings. */
  IImplemSpecifics fImplemSpecif;
  
  /** the output file. */
  Stream fOut;
  
  /** the current bcel repository used. */
  final Repository fRepos;
  
  
  /** the current base directory, from where to generate the files. */ 
  private File fBaseDir;
  
  /**
   * Initialize an executor object.
   * @param repos the bcel repository
   * @param implemSpecif the specific implementation elements
   * @param methodHandler the method handler
   * @param out the output file
   * @param dico the dictionnary associated with the executor
   */
  public ABasicExecutor(final Repository repos, final IImplemSpecifics implemSpecif, 
                        final MethodHandler methodHandler, final Util.Stream out, 
                        final Dictionary dico, final File baseDir) {
    fImplemSpecif = implemSpecif;
    fMethodHandler = methodHandler;
    fRepos = repos;
    fOut = out;
    fDico = dico;
    fBaseDir = baseDir;
  }
  
  public void setBaseDir(File baseDir) {
    fBaseDir = baseDir;
  }
  public File getBaseDir() {
    return fBaseDir;
  }
  
  /**
   * A constructor that initialize all the variables from another
   * object.
   * @param be the BasicExecutor to get the initialization from
   */
  public ABasicExecutor(final ABasicExecutor be) {
    this(be.fRepos, be.fImplemSpecif, be.fMethodHandler, be.fOut, be.fDico, be.fBaseDir);
  }
  
  /**
   * An executor must be able to start somehow.
   * This represents the main entry point of the executor.
   * @throws ClassNotFoundException if a class cannot be resolved
   * @throws IOException in case of write problem
   */
  public abstract void start() throws ClassNotFoundException, IOException;
  
  /**
   * Returns the current repository.
   * @return should not be null
   */
  public final Repository getRepository() {
    return fRepos;
  }
  /**
   * The current output stream of the executor.
   * @return an output stream
   */
  public final Stream getOut() {
    return fOut;
  }
  
  /**
   * Returns the current data structure that
   * stock Coq method's name.
   * @return a method handler instance
   */
  public final MethodHandler getMethodHandler() {
    return fMethodHandler;
  }
  
}
