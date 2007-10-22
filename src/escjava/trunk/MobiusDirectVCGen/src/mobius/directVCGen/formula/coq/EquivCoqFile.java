package mobius.directVCGen.formula.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;

import escjava.sortedProver.NodeBuilder.STerm;

public class EquivCoqFile extends CoqFile {
  
  /** the name of the vc file name: "byteVc". */
  private static final String fVcFileName = "equivVc";



  public EquivCoqFile(File configDir, File baseDir) throws FileNotFoundException {
    super(configDir, baseDir, fVcFileName);
  }


  
  public void doIt(String classname, String meth, 
                   final STerm term) {
    // bytecode
    final PrintStream out = getOut();
    writeHeader();

    out.println("Lemma l :\nforall os: OperandStack.t, \n" +
        "   " + term + "\n" +
        "<-> \n" +
        "   interp_swp BicoMapAnnotations.anno_prog BicoMapProgram.program\n" + 
        "      (certifiedMethod BicoMapAnnotations.anno_prog " +
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


