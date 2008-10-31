package mobius.directVCGen.bico;

import java.io.File;
import java.io.IOException;

import javafe.ast.TypeDecl;
import javafe.tc.TypeSig;
import javafe.util.ErrorSet;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.translator.JMLAnnotationGenerator;
import escjava.tc.TypeCheck;

/**
 * The class to launch the Bico +.
 * Maybe temporary as it will be in a near future directly included
 * inside the Mobius tool (hopefully).
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Main extends mobius.directVCGen.Main {


  /**
   * Create a main object from a base directory.
   * @param basedir The directory where to stock all the files
   * @param bicodir bicodir the path to bicolano archive
   * @param classPath the class path where to look for the files.
   */
  public Main(final File basedir, 
              final File bicodir, final String classPath) {
    super(basedir, bicodir, classPath);
    
  }


  /**
   * Run the stage1 (just type checking and pretty print)
   * and then runs the VCGen.
   * @param td the type declaration to check
   * @return <code>false</code> don't ask why
   */
  //@ requires td != null;
  //@ requires (* td is not from a binary file. *);
  public boolean processTD(final TypeDecl td) {
    final int errorCount = ErrorSet.errors;

    final long startTime = currentTime();
    final IAnnotationGenerator gen = new JMLAnnotationGenerator(); 
    Lookup.clear(gen);
    // preparation: type checking + package dir creation
    final TypeSig sig = TypeCheck.inst.getSig(td);
    sig.typecheck();

    try {
      processTDstage1(td, sig, errorCount);
    } 
    catch (IOException e) {
      System.err.println("Generation failed.");
      e.printStackTrace();
    }
    fOut.println("[" + timeUsed(startTime) + "]\n");

    doBcVCGen(sig, gen); 
    return false;

  }
  
  /**
   * The main entry point.
   * @param args ESC/Java styles of args - most of them will be
   * ignored anyway -
   */
  public static void main(final /*@ non_null @*/String[] args) {
    // the first argument is the output dir
    if (args.length < 2) {
      fOut.println("I need at least 2 arguments the output directory, " + 
                  "and the path to the file bicolano.jar");
      return;
    }

    final String[] escargs = new String[args.length - 2];
    for (int i = 2; i < args.length; i++) {
      escargs[i - 2] = args[i];
    }

    try {

      fOut.println("Configuring everything:\n");
      final File basedir = getBaseDir(args);
      
      // Configuring bicolano and all the preludes
      final File bicodir = new File(args[1]);
      final String cp = getClassPath(args);
      
      
      // Launching the beast
      final Main m = new Main(basedir, bicodir, cp);
      m.start(escargs);
      
    }
    catch (IOException e1) {
      e1.printStackTrace();
      return;
    }
  }




}
