package freeboogie;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.List;

import com.google.common.collect.Lists;
import genericutils.Logger;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;
import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import freeboogie.ast.Program;
import freeboogie.ast.Transformer;
import freeboogie.backend.ProverException;
import freeboogie.cli.FbCliOptionsInterface;
import freeboogie.cli.FbCliParser;
import freeboogie.cli.FbCliUtil;
import freeboogie.parser.FbLexer;
import freeboogie.parser.FbParser;
import freeboogie.tc.TcInterface;
import freeboogie.tc.ForgivingTc;
import freeboogie.tc.TypeChecker;
import freeboogie.vcgen.*;

import static freeboogie.cli.FbCliOptionsInterface.*;
import static freeboogie.cli.FbCliOptionsInterface.LogCategories;
import static freeboogie.cli.FbCliOptionsInterface.LogLevel;

/**
  Handles the main pipeline of the application. The input/output
  data for various stages is one of: (1) a stream in the
  Boogie language format, (2) AST for representing Boogie, (3)
  s-expressions, (4) list of errors. The parser takes (1) as
  input and produces (2). Then there are a few stages that take
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

  private TcInterface tc;
  private HavocMaker havocMaker;
  private LoopCutter loopCutter;
  private CallDesugarer callDesugarer;
  private HavocDesugarer havocDesugarer;
  private SpecDesugarer specDesugarer;
  private Passivator passivator;
  private VcGenerator vcgen;

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
      normal("Nothing to do. Try --help.");
    for (File f : opt.getFiles()) {
      verbose("Processing " + f.getPath());
      parse(f);
      if (boogie.ast == null || !typecheck())
        continue; // parse error or empty input
      transformBoogie();
      try {
        vcgen.process(boogie.ast, tc); // process implementations one by one
      } catch (ProverException e) {
        assert false: "todo: handle in vcgenerator";
      }
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
      verbose("Can't write to log file " + opt.getLogFile() + ".");
    }
    log.level(opt.getLogLevel());
    for (LogCategories c : opt.getLogCategories()) log.enable(c);
    log.verbose(true);
  }

  private void initStages() {
    switch (opt.getBoogieVersion()) {
      case ONE: tc = new ForgivingTc(); break;
      default: tc = new TypeChecker(); break;
    }
  }

  private void parse(File f) {
    try {
      FbLexer lexer = new FbLexer(new ANTLRFileStream(f.getPath()));
      CommonTokenStream tokens = new CommonTokenStream(lexer);
      FbParser parser = new FbParser(tokens);
      parser.fileName = f.getName();
      boogie = new Program(parser.program(), parser.fileName);
    } catch (IOException e) {
      normal("Can't read " + f.getName() + ": " + e.getMessage());
      boogie = new Program(null, null);
    } catch (RecognitionException e) {
      verbose("Can't parse " + f.getName() + ": " + e.getMessage());
      boogie = new Program(null, null);
    }
  }

  private boolean typecheck() {
    try {
      boogie = tc.process(boogie);
    } catch (ErrorsFoundException e) {
      e.report();
      return true;
    }
    return false;
  }

  private void transformBoogie() {
    List<Transformer> phases = Lists.newArrayList();
    boogie = havocMaker.process(boogie, tc);

    assert false : "todo";
  }

  private void normal(String s) {
    out.say(ReportOn.MAIN, ReportLevel.NORMAL, s);
  }

  private void verbose(String s) {
    out.say(ReportOn.MAIN, ReportLevel.VERBOSE, s);
  }

  public static void badUsage() {
    System.out.println("I don't understand what you want. Try --help.");
    System.exit(1);
  }
}
