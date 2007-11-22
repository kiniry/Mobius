package mobius.directVCGen.formula.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;

import mobius.directVCGen.formula.Util;

import javafe.ast.RoutineDecl;

import escjava.sortedProver.NodeBuilder.STerm;

public class EquivCoqFile extends CoqFile {
  
  /** the name of the vc file name: "byteVc". */
  private static final String fVcFileName = "equivVc";



  public EquivCoqFile(File configDir, File baseDir) throws FileNotFoundException {
    super(configDir, baseDir, fVcFileName);
  }


  
  public void doIt(final RoutineDecl decl, final STerm term) {
    // bytecode
    final PrintStream out = getOut();
    writeHeader();

    String methSig = Util.getMethodSigModule(decl);
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
  
  @Override
  protected String getDefaultProof() {
    final String proof = "   prettyfy.\n" +
                         "   nintros; repeat (split; nintros); cleanstart.\n";
    return proof;
  }
}


