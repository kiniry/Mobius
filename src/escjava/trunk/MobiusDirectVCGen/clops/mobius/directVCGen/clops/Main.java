package mobius.directVCGen.clops;

import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;

import javafe.util.AssertionFailureException;

/**
 * The class to launch the MobiusDirectVCGen.
 * Maybe temporary as it will be in a near future directly included
 * inside the Mobius tool (hopefully).
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Main {

  /** the main output stream. */
  protected static PrintStream fOut = System.out;

  /** */
  private Main() { }

  /**
   * The main entry point.
   * @param args ESC/Java styles of args - most of them will be
   * ignored anyway -
   */
  public static void main(final /*@ non_null @*/String[] args) {
    // the first argument is the output dir
    
    DirectVCGenParser parser;
    try {
      parser = new DirectVCGenParser();
    } 
    catch (InvalidOptionPropertyValueException e) {
      e.printStackTrace();
      return;
    }
    if (!parser.parse(args)) {
      System.err.println("Bad usage!");
      System.err.println("(try java -jar DirectVCGen.jar -help)");
      return;
    }
    final DirectVCGenOptionsInterface opt = parser.getOptionStore();
    
    if (opt.isHelpSet()) {
      fOut.println("I need at least 2 arguments:\n" +
                   " - the output directory and\n+" +
                   " - the path to the file bicolano.jar");
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
      System.out.println("Launching...");
      final  mobius.directVCGen.Main m = new mobius.directVCGen.Main(basedir, bicodir, cp);
      m.start(escargs);
      System.out.println("I'm finished!");
      
    }
    catch (IOException e1) {
      e1.printStackTrace();
      return;
    }
    catch (AssertionFailureException e) {
      e.printStackTrace();
    }
  }


  /**
   * Changes the output stream where some log informations are written.
   * @param out the output stream with which to replace the current one
   */
  public static void setOut(final OutputStream out) {
    fOut = new PrintStream(out);
  }

}
