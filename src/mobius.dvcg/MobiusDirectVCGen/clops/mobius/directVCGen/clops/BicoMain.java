package mobius.directVCGen.clops;

import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;

import java.io.File;
import java.io.IOException;

import javafe.ast.TypeDecl;
import javafe.tc.TypeSig;
import javafe.util.ErrorSet;
import mobius.directVCGen.clops.bico.BicoPlusOptionsInterface;
import mobius.directVCGen.clops.bico.BicoPlusParser;
import mobius.directvcgen.bico.IAnnotationGenerator;
import mobius.directvcgen.formula.Lookup;
import mobius.directvcgen.translator.JMLAnnotationGenerator;
import escjava.tc.TypeCheck;

/**
 * The class to launch the Bico +.
 * Maybe temporary as it will be in a near future directly included
 * inside the Mobius tool (hopefully).
 * @author J. Charles (julien.charles@inria.fr)
 */
public class BicoMain extends mobius.directvcgen.Main {
  public static final String BAD_USAGE_MSG = 
    "Bad usage!\n" +
    "(try java -jar DirectVCGen.jar -help)";
  public static final String HELP_MSG = 
    "I need at least 2 arguments:\n" +
    " - the output directory and\n+" +
    " - the path to the file bicolano.jar";

  /**
   * Create a main object from a base directory.
   * @param basedir The directory where to stock all the files
   * @param bicodir bicodir the path to bicolano archive
   * @param classPath the class path where to look for the files.
   */
  public BicoMain(final File basedir, 
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
   * @throws InvalidOptionValueException 
   * @throws AutomatonException 
   */
  public static void main(final /*@ non_null @*/String[] args) {
    BicoPlusParser parser;
    try {
      parser = new BicoPlusParser();
    } 
    catch (InvalidOptionPropertyValueException e) {
      e.printStackTrace();
      return;
    }
    try {
      if (!parser.parse(args)) {
        System.err.println(BAD_USAGE_MSG);
        return;
      }
    }
    catch (AutomatonException e) {
      e.printStackTrace();
      return;
    }
    catch (InvalidOptionValueException e) {
      e.printStackTrace();
      return;
    }
    final BicoPlusOptionsInterface opt = parser.getOptionStore();
    
    if (opt.isHelpSet()) {
      fOut.println(HELP_MSG);
      return;
    }

    final String[] escargs = new String[args.length - 2];
    for (int i = 2; i < args.length; i++) {
      escargs[i - 2] = args[i];
    }

    try {
      fOut.println("Configuring everything:\n");
      final File basedir = opt.getOutputDir();
      final File bicodir = opt.getFormalisationJar();
      final String cp = opt.isClassPathSet() ? opt.getClassPath() : "";
      
      // Launching the beast
      final BicoMain m = new BicoMain(basedir, bicodir, cp);
      m.start(escargs);
      
    }
    catch (IOException e1) {
      e1.printStackTrace();
      return;
    }
  }




}
