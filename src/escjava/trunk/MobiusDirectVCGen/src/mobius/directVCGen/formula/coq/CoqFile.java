package mobius.directVCGen.formula.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.List;
import java.util.Set;

import mobius.directVCGen.formula.Formula;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.NodeBuilder.FnSymbol;
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




  /**
   * Construct an object used to print a proof obligation in a file.
   * @param configDir the library directory
   * @param baseDir the directory where the generated file should be put 
   * @param name the preferred name the file should have
   * @throws FileNotFoundException if opening the file fails
   */
  public CoqFile(final File configDir, final File baseDir, 
                 final String name) throws FileNotFoundException {
    fOut = new PrintStream(new FileOutputStream(new File(baseDir, 
                              name + suffix)));
    fBase = configDir.toString();
  }

  /**
   * Write the proof obligation represented by the
   * given term.
   * @param term the formula representing the proof obligation
   */
  public void writeProof(final STerm term) {
    fOut.println("Lemma l:\n" + term + ".");
    fOut.println("Proof.");
    fOut.println("intros; repeat (split; intros).\n\nQed.");
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
   * Write the definitions for coq: basically it writes class
   * definitions; fields to declare; and special magickal symbols.
   * @param symToDeclare Special relation symbols to declare
   * @param fieldsToDeclare the fields to declare
   * @param classNames the class names to declare
   */
  public void writeDefs(final List<FnSymbol> symToDeclare, 
                        final Set<QuantVariable> fieldsToDeclare, 
                        final List<String> classNames) {
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

    
    fOut.println();
    for (FnSymbol sym : symToDeclare) {
      fOut.print("Variable " + sym.name + ": ");
      final STerm [] terms = Formula.generateTypes(sym.argumentTypes);
      for (STerm t: terms) {
        final String str = t.toString();
        fOut.print(str + " -> ");
      }
      fOut.println(Formula.generateType(sym.retType) + ".");
    }

    fOut.println();
    
    fOut.println("Open Local Scope Z_scope.");
  }

}
