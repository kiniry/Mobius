package mobius.bmlvcgen.main;

import mobius.bmlvcgen.args.exceptions.ArgException;
import mobius.bmlvcgen.finder.ClassFinder;
import mobius.bmlvcgen.finder.DefaultClassFinder;
import mobius.bmlvcgen.logging.DefaultLoggerFactory;
import mobius.bmlvcgen.logging.Logger;

/**
 * Main class of the application.
 * Creates and initializes an environment and
 * passes control to BmlVCGen.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public final class Main {
  private final Env env;

  private final Logger logger;

  private Main(final Env env) {
    this.env = env;
    logger = env.getLoggerFactory().getLogger(Main.class);
  }
  
  /**
   * Entry point.
   * @param args Command line arguments.
   */
  public static void main(final String... args) {
    final Env env = new Env(DefaultLoggerFactory.getInstance());
    final Main main = new Main(env);
    main.run(args);
  }
  
  private void run(final String... args) {
    logger.info("Starting BmlVCGen");
    logger.debug("Loglevel is set to DEBUG.");
    if (parseArgs(args)) {
      env.getArgs().log(logger);
      final ClassFinder classFinder = new DefaultClassFinder(env);
      env.setClassFinder(classFinder);
      final BmlVCGen vcgen = new BmlVCGen(env);
      vcgen.run();
    } else {
      printHelp();
    }
    logger.info("BmlVCGen exit.");
  }

  // Parse arguments, 
  // return true unless arguments are invalid or help
  // was requested.
  private boolean parseArgs(final String... args) {
    final Args a = new Args();
    try {
      a.parse(args);
    } catch (ArgException e) {
      // TODO: Print localized message in stdout or stderr.
      logger.error("Invalid arguments");
      logger.error(e.getMessage());
      return false;
    }
    env.setArgs(a);
    return !a.shouldPrintHelp();
  }

  // Print help message.
  private void printHelp() {
    // TODO: Localize, extend.
    System.out.println("Valid options: ");
    System.out.println("   -c,--classpath" + 
                       "   Set classpath used when loading classes.");
    System.out.println("   -s,--systempath" + 
                       "   Append system path to classpath.");
    System.out.println("   -b,--bicolano " + 
                       "   Set path to bicolano JAR.");
    System.out.println("   -o,--output" + 
                       "   Set output directory.");
    System.out.println("   -h,--help" + 
                       "   Display help message.");
  }

}
