package mobius.directVCGen.formula.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;

import javafe.ast.RoutineDecl;

import mobius.directVCGen.formula.Util;

/**
 * This class represents a bytecode proof obligation file.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class BcCoqFile extends CoqFile {
  
  /** the name of the vc file name: "byteVc". */
  private static final String fVcFileName = "byteVc";


  /**
   * Creates a new Bytecode vc file representation.
   * @param baseDir the root directory containing the libraries 
   * @param workingDir the directory containing this file
   * @throws FileNotFoundException if the vc file cannot be created
   */
  public BcCoqFile(final File baseDir, final File workingDir) throws FileNotFoundException {
    super(baseDir, workingDir, fVcFileName);
  }

  /**
   * Writes the proof obligation in the file.
   * @param decl the routine from which the proof obligation is the target
   */
  public void doIt(final RoutineDecl decl) {
    // bytecode
    final PrintStream out = getOut();
    writeHeader();

    out.println("Lemma l :\n" +  
      "  interp_swp BicoAnnotations.anno_prog BicoProgram.program\n" + 
      "    (certifiedMethod BicoAnnotations.anno_prog " +
                                    Util.getMethodSigModule(decl) + " " +
                                    Util.getMethodModule(decl) + " " + 
                                    Util.getMethodAnnotModule(decl) + ".spec).");
    out.println("Proof with auto.");
    out.print(getProof());
    out.println("Qed.");
  }
  
  /**
   * Returns the default proof obligation.
   * @return <code>prettyfy. nintros; repeat (split; nintros); cleanstart.</code>
   */
  @Override
  protected String getDefaultProof() {
    final String proof = "   prettyfy.\n" +
                         "   nintros; repeat (split; nintros); cleanstart.\n";
    return proof;
  }
}


