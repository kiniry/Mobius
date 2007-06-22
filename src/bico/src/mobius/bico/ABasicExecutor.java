package mobius.bico;

import java.io.IOException;
import java.io.PrintStream;

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
  PrintStream fOut;
  
  /** the current bcel repository used. */
  final Repository fRepos;
  
  /**
   * Initialize an executor object.
   * @param repos the bcel repository
   * @param implemSpecif the specific implementation elements
   * @param methodHandler the method handler
   * @param out the output file
   * @param dico the dictionnary associated with the executor
   */
  public ABasicExecutor(final Repository repos, final IImplemSpecifics implemSpecif, 
                        final MethodHandler methodHandler, final PrintStream out, 
                        final Dictionary dico) {
    fImplemSpecif = implemSpecif;
    fMethodHandler = methodHandler;
    fRepos = repos;
    fOut = out;
    fDico = dico;
  }
  
  /**
   * A constructor that initialize all the variables from another
   * object.
   * @param be the BasicExecutor to get the initialization from
   */
  public ABasicExecutor(final ABasicExecutor be) {
    this(be.fRepos, be.fImplemSpecif, be.fMethodHandler, be.fOut, be.fDico);
  }
  
  /**
   * An executor must be able to start somehow.
   * This represents the main entry point of the executor.
   * @throws ClassNotFoundException if a class cannot be resolved
   * @throws IOException in case of write problem
   */
  public abstract void start() throws ClassNotFoundException, IOException;
  
}
