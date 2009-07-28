package mobius.directVCGen.formula.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;

import mobius.directVCGen.formula.Util;

import javafe.ast.RoutineDecl;

import escjava.sortedProver.NodeBuilder.STerm;

/**
 * This class represents the file which contains the 
 * equivalence proof obligation.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class EquivCoqFile extends CoqFile {
  
  /** the name of the vc file name: "byteVc". */
  private static final String fVcFileName = "equivVc";


  /**
   * Creates a new Equivalence vc file representation.
   * @param baseDir the root directory containing the libraries 
   * @param workingDir the directory containing this file
   * @throws FileNotFoundException if the vc file cannot be created
   */
  public EquivCoqFile(final File baseDir, final File workingDir) throws FileNotFoundException {
    super(baseDir, workingDir, fVcFileName);
  }


  /**
   * Writes the proof obligation.
   * @param decl the routine from which the proof obligation 
   * is generated
   * @param term the source vc
   */
  public void doIt(final RoutineDecl decl, final STerm term) {
    // bytecode
    final PrintStream out = getOut();
    writeHeader();

    final String methSig = Util.getMethodSigModule(decl);
    out.println("Lemma l :\n" +
        "   " + term + "\n" +
        "<-> \n" +
        "   interp_swp BicoAnnotations.anno_prog BicoProgram.program\n" + 
        "      (certifiedMethod BicoAnnotations.anno_prog " +
                                    methSig + " " +
                                    Util.getMethodModule(decl) + " " +
                                    Util.getMethodAnnotModule(decl) + ".spec).");
    out.println("Proof with assumption.");
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


