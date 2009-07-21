package mobius.directvcgen.clops;

import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import mobius.directvcgen.clops.dvcg.DirectVCGenOptionsInterface;
import mobius.directvcgen.clops.dvcg.DirectVCGenParser;
import mobius.directvcgen.Main;

import javafe.util.AssertionFailureException;

/**
 * The class to launch the MobiusDirectVCGen.
 * Maybe temporary as it will be in a near future directly included
 * inside the Mobius tool (hopefully).
 * @author J. Charles (julien.charles@inria.fr)
 */
public class DirectVCGenMain {

  /** the main output stream. */
  protected static PrintStream fOut = System.out;

  public static final String BAD_USAGE_MSG = 
        "Bad usage!\n" +
        "(try java -jar DirectVCGen.jar -help)";
  public static final String HELP_MSG = 
    "I need at least 2 arguments:\n" +
    " - the output directory and\n+" +
    " - the path to the file bicolano.jar";
  /** */
  private DirectVCGenMain() { }

  /**
   * The main entry point.
   * @param args ESC/Java styles of args - most of them will be
   * ignored anyway -
   * @throws InvalidOptionValueException 
   * @throws AutomatonException 
   */
  public static void main(final /*@ non_null @*/String[] args) throws AutomatonException, InvalidOptionValueException {
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
      System.err.println(BAD_USAGE_MSG);
      return;
    }
    final DirectVCGenOptionsInterface opt = parser.getOptionStore();
    
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
      System.out.println("Launching...");
      final  Main m = new Main(basedir, bicodir, cp);
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
