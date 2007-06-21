package mobius.bico;

import java.io.IOException;
import java.io.PrintStream;

import mobius.bico.dico.CamlDictionary;
import mobius.bico.dico.Dictionary;
import mobius.bico.implem.IImplemSpecifics;

import org.apache.bcel.util.Repository;

public abstract class ABasicExecutor {
  
  
  final MethodHandler fMethodHandler;

  final Dictionary fDico = new CamlDictionary();
  /** Bicolano's implementations specific handlings. */
  IImplemSpecifics fImplemSpecif;
  /** the output file. */
  PrintStream fOut;
  /** the current bcel repository used. */
  final Repository fRepos;
  
  public ABasicExecutor(Repository repos, IImplemSpecifics implemSpecif, 
                        MethodHandler methodHandler, PrintStream out) {
    fImplemSpecif = implemSpecif;
    fMethodHandler = methodHandler;
    fRepos = repos;
    fOut = out;
  }
  
  public ABasicExecutor(ABasicExecutor be) {
    this(be.fRepos, be.fImplemSpecif, be.fMethodHandler, be.fOut);
  }
  
  public abstract void start() throws ClassNotFoundException, IOException;
  
}
