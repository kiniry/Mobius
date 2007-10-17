package mobius.directVCGen.formula.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;
import java.io.PrintStream;

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

  private String fOldProof;

  /**
   * Construct an object used to print a proof obligation in a file.
   * @param configDir the library directory
   * @param baseDir the directory where the generated file should be put 
   * @param name the preferred name the file should have
   * @throws FileNotFoundException if opening the file fails
   */
  public CoqFile(final File configDir, final File baseDir, 
                 final String name) throws FileNotFoundException {
    final File f = new File(baseDir, name + suffix);
    getOldProof(f);
    fOut = new PrintStream(new FileOutputStream(f));
    fBase = configDir.toString();

  }
  
  /**
   * Construct an object used to print a proof obligation in a file.
   * The name is the default one ("sourceVc").
   * @param configDir the library directory
   * @param baseDir the directory where the generated file should be put 
   * @throws FileNotFoundException if opening the file fails
   */
  public CoqFile(final File configDir, final File baseDir) throws FileNotFoundException {
     this (configDir, baseDir, "sourceVc");
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
    fOut.println("Add LoadPath \"" + fBase + "\".\n" +
                 "Add LoadPath \"" + fBase + File.separator + "Formalisation\".\n" +
                 "Add LoadPath \"" + fBase + File.separator + "Formalisation" +
                 File.separator + "Bicolano" + "\".\n" +
                 "Add LoadPath \"" + fBase + File.separator + "Formalisation" +
                 File.separator + "Logic" + "\".\n" +
                 "Add LoadPath \"" + fBase + File.separator + "Formalisation" +
                 File.separator + "Library" + "\".\n" +
                 "Add LoadPath \"" + fBase + File.separator + "Formalisation" +
                 File.separator + "Library" + 
                 File.separator + "Map" + "\".\n");

    fOut.println("Require Import BicoMap_annotations.");
    fOut.println("Require Import defs_types.");
    fOut.println("Import BicoMapAnnotations P Mwp.");
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
  
  protected String getDefaultProof() {
    return "   nintros; repeat (split; nintros); cleanstart.\n";
  }
  
  public String getProof() {
    return fOldProof;
  }
  
  private void getOldProof(File f) {
    if (f.exists()) {
      fOldProof = "";
      try {
        final LineNumberReader reader = new LineNumberReader(new FileReader(f));
        String line = reader.readLine();
        //System.out.println (f + "\n" + line);
        while ((line != null) && !line.startsWith("Proof with")) {
          line = reader.readLine();
        }
        line = reader.readLine();
        while ((line != null) && !line.startsWith("Qed.")) {
          fOldProof = fOldProof + line + "\n";
          line = reader.readLine();
          
        }
        reader.close();
//        System.out.println (fOldProof);
       
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
