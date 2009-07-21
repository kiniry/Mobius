package mobius.bmlvcgen.main;

import java.util.ArrayList;
import java.util.Collection;

import mobius.bmlvcgen.args.ArgParser;
import mobius.bmlvcgen.args.annot.AnnotReader;
import mobius.bmlvcgen.args.annot.CmdParam;
import mobius.bmlvcgen.args.exceptions.ArgException;
import mobius.bmlvcgen.logging.Logger;
import mobius.bmlvcgen.util.StringUtil;

/**
 * Objects of this class contain values set 
 * using command line parameters.
 * These values can also be set directly, 
 * if BmlVCGen is used as a library.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public final class Args {
  private String classpath;
  private boolean addSystemPath;
  private String outputDir;
  private String bicolanoJar;
  private Collection<String> classNames;
  private boolean printHelp;

  private ArgParser parser;

  /**
   * Constructor. Creates Args object with
   * default values.
   */
  public Args() {
    // Set default values.
    classpath = StringUtil.concatPaths(
                  System.getProperty("sun.boot.class.path", ""),
                  System.getProperty("java.class.path", ""));
    addSystemPath = false;
    outputDir = "output";
    bicolanoJar = "bicolano.jar";
    printHelp = false;
    classNames = new ArrayList<String>();
  }

  /**
   * Parse arguments and modify stored values.
   * @param args Arguments.
   * @throws ArgException If arguments are invalid.
   */
  public void parse(final String... args) throws ArgException {
    if (parser == null) {
      parser = new ArgParser();
      AnnotReader.findOptions(this, parser);
    }
    classNames.clear();
    for (final String nonOptionArg : parser.parse(args)) {
      classNames.add(nonOptionArg);
    }
  }

  /**
   * Log argument values.
   * @param logger Logger to use.
   */
  public void log(final Logger logger) {
    logger.info("Configuration: ");
    logger.info("   Classpath: %1$s", classpath);
    if (addSystemPath) {
      logger.info("   System classpath used.");
    }
    logger.info("   Bicolano directory: %1$s", bicolanoJar);
    logger.info("   Output directory: %1$s", outputDir);
    if (classNames.size() > 0) {
      logger.info("Classes to be processed:");
      for (final String name : classNames) {
        logger.info("   %1$s", name);
      }
    } else {
      logger.info("No classes to process.");
    }
  }

  /**
   * Set classpath value.
   * @param classpath Classpath.
   */
  @CmdParam(shortName = 'c', longName = "classpath")
  public void setClasspath(final String classpath) {
    this.classpath = classpath;
  }

  /**
   * Set path to bicolano jar.
   * @param bicolanoJar Path to bicolano.
   */
  @CmdParam(shortName = 'b', longName = "bicolano")
  public void setBicolanoJar(final String bicolanoJar) {
    this.bicolanoJar = bicolanoJar;
  }

  /**
   * Set output directory.
   * @param outputDir Output directory.
   */
  @CmdParam(shortName = 'o', longName = "output")
  public void setOutputDir(final String outputDir) {
    this.outputDir = outputDir;
  }

  /**
   * Request printing of help message.
   */
  @CmdParam(shortName = 'h', longName = "help")
  public void requestHelp() {
    printHelp = true;
  }

  /**
   * Append system path to specified classpath.
   */
  @CmdParam(shortName = 's', longName = "systempath")
  public void requestAddSystemPath() {
    addSystemPath = true;
  }
  
  /**
   * Get value of classpath.
   * @return Classpath.
   */
  public String getClasspath() {
    return classpath;
  }

  /**
   * Get path to bicolano jar.
   * @return Path to bicolano.
   */
  public String getBicolanoJar() {
    return bicolanoJar;
  }

  /**
   * Get output directory.
   * @return Output directory.
   */
  public String getOutputDir() {
    return outputDir;
  }

  /**
   * Should help message be printed?
   * @return True iff help was requested.
   */
  public boolean shouldPrintHelp() {
    return printHelp;
  }
  
  /**
   * Get names of classes to be processed.
   * @return Collection of class names.
   */
  public Collection<String> getClassNames() {
    return classNames;
  }
  
  /**
   * Should system path be appended to classpath.
   * @return .
   */
  public boolean isAddSystemPath() {
    return addSystemPath;
  }
}
