package mobius.directVCGen.formula.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;

import javafe.ast.RoutineDecl;

import mobius.directVCGen.formula.Util;

public class BcCoqFile extends CoqFile {
  
  /** the name of the vc file name: "byteVc". */
  private static final String fVcFileName = "byteVc";



  public BcCoqFile(final File configDir, final File baseDir) throws FileNotFoundException {
    super(configDir, baseDir, fVcFileName);
  }


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
  
  @Override
  protected String getDefaultProof() {
    final String proof = "   prettyfy.\n" +
                         "   nintros; repeat (split; nintros); cleanstart.\n";
    return proof;
  }
}


