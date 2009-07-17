package freeboogie;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;

import genericutils.Logger;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;
import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import freeboogie.ast.Program;
import freeboogie.cli.FbCliOptionsInterface;
import freeboogie.cli.FbCliParser;
import freeboogie.cli.FbCliUtil;
import freeboogie.parser.FbLexer;
import freeboogie.parser.FbParser;

import static freeboogie.cli.FbCliOptionsInterface.*;
import static freeboogie.cli.FbCliOptionsInterface.LogCategories;
import static freeboogie.cli.FbCliOptionsInterface.LogLevel;

/**
  Handles the main pipeline of the application. The input/output
  data for various stages is one of: (1) a stream in the
  Boogie language format, (2) AST for representing Boogie, (3)
  s-expressions, (4) list of errors. The parser takes (1) as
  input and prouces (2). Then there are a few stages that take
  (2) as input and produce (2). The VC generation phase takes
  (2) as input and produces (3) as output. There are then a
  few stages that take (3) as input an produce (3) as output.
  Finally, the backend takes (3) as input and produces (4).

  NOTE: this is under development now and will replace both
  freeboogie.Main and freeboogie.vcgen.VcGenerator.
 */
public class AlternativeMain {

  private FbCliOptionsInterface opt;
  private Logger<ReportOn, ReportLevel> out;
  private Logger<LogCategories, LogLevel> log;
  private Program boogie;

  /** Process the command line and call {@code run()}. */
  public static void main(String[] args) throws Exception {
    FbCliParser p = new FbCliParser();
    try { if (!p.parse(args)) badUsage(); }
    catch (InvalidOptionValueException e) { badUsage(); }
    AlternativeMain m = new AlternativeMain();
    m.run(p.getOptionStore());
  }

  public void run(FbCliOptionsInterface opt) {
    this.opt = opt;
    if (opt.isHelpSet()) {
      FbCliUtil.printUsage();
      return;
    }
    setupLogging();
    initStages();

    if (opt.getFiles().isEmpty())
      out.say(ReportOn.MAIN, ReportLevel.NORMAL, "Nothing to do. Try --help.");
    for (File f : opt.getFiles()) {
      out.say(ReportOn.MAIN, ReportLevel.VERBOSE, "Processing " + f.getPath());
      parse(f);
      if (boogie.ast == null || !typecheck())
        continue; // parse error or empty input
      transformBoogie();
      vcgen();
      transformVc();
      askProver();
    }
  }

  private void setupLogging() {
    out = Logger.<ReportOn, ReportLevel>get("out");
    log = Logger.<LogCategories, LogLevel>get("log");
    out.sink(System.out); 
    out.level(opt.getReportLevel());
    for (ReportOn c : opt.getReportOn()) out.enable(c);
    try { log.sink(opt.getLogFile()); }
    catch (IOException e) { 
      out.say(
        ReportOn.MAIN,
        ReportLevel.VERBOSE, 
        "Can't write to log file " + opt.getLogFile() + ".");
    }
    log.level(opt.getLogLevel());
    for (LogCategories c : opt.getLogCategories()) log.enable(c);
    log.verbose(true);
  }

  private void initStages() {
    assert false : "todo";
  }

  private void parse(File f) {
    try {
      FbLexer lexer = new FbLexer(new ANTLRFileStream(f.getPath()));
      CommonTokenStream tokens = new CommonTokenStream(lexer);
      FbParser parser = new FbParser(tokens);
      parser.fileName = f.getName();
      boogie = new Program(parser.program(), parser.fileName);
    } catch (IOException e) {
      out.say(
        ReportOn.MAIN,
        ReportLevel.NORMAL,
        "Can't read " + f.getName() + ": " + e.getMessage());
      boogie = new Program(null, null);
    } catch (RecognitionException e) {
      out.say(
        ReportOn.MAIN,
        ReportLevel.VERBOSE,
        "Can't parse " + f.getName() + ": " + e.getMessage());
      boogie = new Program(null, null);
    }
  }

  private boolean typecheck() {
    assert false : "todo";
    return false;
  }

  private void transformBoogie() {
    assert false : "todo";
  }

  private void vcgen() {
    assert false : "todo";
  }

  private void transformVc() {
    assert false : "todo";
  }

  private void askProver() {
    assert false : "todo";
  }

  public static void badUsage() {
    System.out.println("I don't understand what you want. Try --help.");
    System.exit(1);
  }
}
