package mobius.directVCGen.formula.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;
import java.io.PrintStream;
import java.util.List;

import mobius.directVCGen.formula.Util;

import escjava.sortedProver.NodeBuilder.STerm;

/**
 * This class is used to print the proof obligations to a file Coq
 * would be able to handle. The path to bicolano is needed for 
 * everything to work.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CoqFile {
  /** the suffix used for the Coq files. */
  public static final String suffix = ".v";
  
  /** the stream to print to the target file. */
  private PrintStream fOut;

  /** the name of the directory which contains bicolano's library files. */
  private String fBase;

  /** the script containing the old proof. */
  private String fOldProof;

  /**
   * Construct an object used to print a proof obligation in a file.
   * @param baseDir the library directory
   * @param workingDir the directory where the generated file should be put 
   * @param name the preferred name the file should have
   * @throws FileNotFoundException if opening the file fails
   */
  public CoqFile(final File baseDir, final File workingDir, 
                 final String name) throws FileNotFoundException {
    final File f = new File(workingDir, name + suffix);
    getOldProof(f);
    fOut = new PrintStream(new FileOutputStream(f));
    fBase = baseDir.toString();

  }
  
  /**
   * Construct an object used to print a proof obligation in a file.
   * The name is the default one ("sourceVc").
   * @param baseDir the library directory
   * @param workingDir the directory where the generated file should be put 
   * @throws FileNotFoundException if opening the file fails
   */
  public CoqFile(final File baseDir, final File workingDir) throws FileNotFoundException {
     this (baseDir, workingDir, "sourceVc");
  }

  /**
   * Write the proof obligation represented by the
   * given term.
   * @param term the formula representing the proof obligation
   */
  public void writeProof(final STerm term) {
    writeHeader();
    fOut.println("Lemma l:\n" + term + ".");
    fOut.println("Proof with auto.");
    fOut.print(getProof());
    fOut.println("Qed.");
  }

  /**
   * Close the file that was currently being written.
   * @throws Throwable an exception in the worst case
   */
  public void finalize() throws Throwable {
    super.finalize();
    fOut.close();
  }



  /**
   * Write the header of the coq file (load path, requires...).
   */
  public void writeHeader() {
    fOut.println("Add LoadPath \"" + fBase + File.separator + "Formalisation\".\n" +
                 "Add LoadPath \"" + fBase + File.separator + "Formalisation" +
                 File.separator + "Bicolano" + "\".\n" +
                 "Add LoadPath \"" + fBase + File.separator + "Formalisation" +
                 File.separator + "Logic" + "\".\n" +
                 "Add LoadPath \"" + fBase + File.separator + "Formalisation" +
                 File.separator + "Library" + "\".\n" +
                 "Add LoadPath \"" + fBase + File.separator + "Formalisation" +
                 File.separator + "Library" + 
                 File.separator + "Map" + "\".\n");

    final List<String> paths = Util.findAllPath(new File(fBase, "classes"));
    for (String p: paths) {
      fOut.println("Add LoadPath \"classes" + p + "\".");
    }
    fOut.println();
    fOut.println("Require Import Bico_annotations.");
    fOut.println("Require Import defs_types.");
    fOut.println("Import BicoAnnotations P Mwp.");
    fOut.println();
    fOut.println("Load \"defs_tac.v\".");
    fOut.println("Open Local Scope Z_scope.");
  }
  
  /**
   * Return the output stream.
   * @return the content of the field {@link #fOut}
   */
  public PrintStream getOut() {
    return fOut;
  }
  
  /**
   * Returns the default proof that should be generated in case
   * the file is newly created.
   * @return a string containing the proof script
   */
  protected String getDefaultProof() {
    return "   nintros; repeat (split; nintros); cleanstart.\n";
  }
  
  
  /**
   * Returns the proof of the file.
   * @return a string representing a proof script
   */
  public String getProof() {
    return fOldProof;
  }
  
  
  private void getOldProof(final File f) {
    if (f.exists()) {
      fOldProof = "";
      try {
        final LineNumberReader reader = new LineNumberReader(new FileReader(f));
        String line = reader.readLine();
        
        while ((line != null) && !line.startsWith("Proof with")) {
          line = reader.readLine();
        }
        line = reader.readLine();
        while ((line != null) && !line.startsWith("Qed.")) {
          fOldProof = fOldProof + line + "\n";
          line = reader.readLine();
          
        }
        reader.close();
       
      } 
      catch (IOException e) {
        e.printStackTrace();
      }
    }
    else {
      fOldProof = getDefaultProof() + "\n";
    }
  }

}
