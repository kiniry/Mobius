package mobius.directVCGen.formula.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;

public class BcCoqFile extends CoqFile {
  
  /** the name of the vc file name: "byteVc". */
  private static final String fVcFileName = "byteVc";



  public BcCoqFile(File configDir, File baseDir) throws FileNotFoundException {
    super(configDir, baseDir, fVcFileName);
  }


  
  public void doIt(String classname, String meth) {
    // bytecode
    final PrintStream out = getOut();
    writeHeader();

    out.println("Lemma l :\n" +  
      "  interp_swp BicoMapAnnotations.anno_prog BicoMapProgram.program\n" + 
      "    (certifiedMethod BicoMapAnnotations.anno_prog " +
                                    classname + "Signature." + meth + " " +
                                    classname + "." + meth + "Method " + 
                                    classname + "Annotations." + meth + ".spec).");
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


