package mobius.directVCGen.formula.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;

public class BcCoqFile extends CoqFile {
  public BcCoqFile(File configDir, File baseDir) throws FileNotFoundException {
    super(configDir, baseDir, "byteVc");
  }


  
  public void doIt(String classname, String meth) {
    // bytecode
    writeHeader(fOut);
//    String classname = "Bill";
//    String meth = "produce_bill";
    fOut.println("Lemma l :\n" +  
      "  interp_swp BicoMapAnnotations.anno_prog BicoMapProgram.program\n" + 
      "    (certifiedMethod BicoMapAnnotations.anno_prog " +
                                    classname + "Signature." + meth + " " +
                                    classname + "." + meth + "Method " + 
                                    classname + "Annotations." + meth + ".spec).");
  }
}
