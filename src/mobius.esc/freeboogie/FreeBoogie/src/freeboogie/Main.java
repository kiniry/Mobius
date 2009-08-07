package freeboogie;

import java.io.*;
import java.util.List;

import com.google.common.base.Function;
import com.google.common.collect.Lists;
import genericutils.Closure;
import genericutils.Logger;
import ie.ucd.clops.runtime.errors.CLError;
import ie.ucd.clops.runtime.options.exception.InvalidOptionValueException;
import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.backend.ProverException;
import freeboogie.cli.FbCliOptionsInterface;
import freeboogie.cli.FbCliParser;
import freeboogie.cli.FbCliUtil;
import freeboogie.dumpers.FlowGraphDumper;
import freeboogie.parser.FbLexer;
import freeboogie.parser.FbParser;
import freeboogie.tc.*;
import freeboogie.vcgen.*;
import static freeboogie.cli.FbCliOptionsInterface.*;
import static freeboogie.cli.FbCliOptionsInterface.LogCategories;
import static freeboogie.cli.FbCliOptionsInterface.LogLevel;

/**
  The entry point for FreeBoogie.

  The function {@code main()} is called, as usual, when the
  program is run from the command line. It parses the command
  line and delegates the other work to {@code run()}, which takes
  an option store as a parameter. An easy way to wrap FreeBoogie
  programatically is to populate an option store and call this
  run method.

  The {@code run()} function loops over all the boogie
  transformation phases enabled by the options. After each phase
  is run, optional debugging data is printed. The Boogie program
  is printed using {@code PrettyPrinter}, the flowgraphs are
  printed using {@code FlowGraphDumper}, and the symbol table is
  printed by some helper code from the {@code Main} class itself.

  @see freeboogie.astutil.PrettyPrinter
  @see freeboogie.dumpers.FlowGraphDumper
 */
public class Main {

  private FbCliOptionsInterface opt;
  private Logger<ReportOn, ReportLevel> out;
  private Logger<LogCategories, LogLevel> log;

  private Program boogie;
  private TcInterface tc;
  private List<Transformer> stages;

  private PrettyPrinter prettyPrinter = new PrettyPrinter();
  private FlowGraphDumper flowGraphDumper = new FlowGraphDumper();

  // used for dumping the symbol table
  private static Function<AtomId, String> nameOfAtomId =
    new Function<AtomId, String>() {
      @Override public String apply(AtomId d) { return d.getId(); }
    };
  private static Function<TypeDecl, String> nameOfType =
    new Function<TypeDecl, String>() {
      @Override public String apply(TypeDecl d) { return d.getName(); }
    };
  private static Function<FunctionDecl, String> nameOfFunctionDecl =
    new Function<FunctionDecl, String>() {
      @Override public String apply(FunctionDecl d) {
        return d.getSig().getName();
      }
    };
  private static Function<Procedure, String> nameOfProcedure =
    new Function<Procedure, String>() {
      @Override public String apply(Procedure d) {
        return d.getSig().getName();
      }
    };
  private static Function<Declaration, String> nameOfVar =
    new Function<Declaration, String>() {
      @Override public String apply(Declaration d) {
        if (d instanceof VariableDecl) return ((VariableDecl)d).getName();
        else return ((ConstDecl)d).getId();
      }
    };

  /** Process the command line and call {@code run()}. */
  public static void main(String[] args) {
    FbCliParser p = new FbCliParser();
    List<CLError> ce = p.parse(args);
    if (!ce.isEmpty()) {
      for (CLError e : ce) {
        // TODO: report errors
      }
      badUsage();
      return;
    }
    Main m = new Main();
    m.run(p.getOptionStore());
  }

  /** Process each file. */
  public void run(FbCliOptionsInterface opt) {
    this.opt = opt;
    if (opt.isHelpSet()) {
      FbCliUtil.printUsage();
      return;
    }
    setupLogging();
    initialize();

    if (opt.getFiles().isEmpty())
      normal("Nothing to do. Try --help.");
    for (File f : opt.getFiles()) {
      verbose("Processing " + f.getPath());
      parse(f);
      if (boogie.ast == null || !typecheck())
        continue; // parse error or empty input
      for (Transformer t : stages) {
        boogie = t.process(boogie, tc);
        dumpState(t.name());
      }
    }
  }

  private void setupLogging() {
    // NOTE: The explicit specialization on the following two
    // lines is there only because of a bug in javac.
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

  private void initialize() {
    // Initialize typechecker.
    switch (opt.getBoogieVersionOpt()) {
      case ONE: tc = new ForgivingTc(); break;
      default: tc = new TypeChecker(); break;
    }

    // Initialize the Boogie transformers.
    stages = Lists.newArrayList();
    stages.add(new Transformer() { @Override public String name() {
      return "Parsing";
    }}); // dummy transformer to report state immediately after parsing
    if (opt.getMakeHavoc()) stages.add(new HavocMaker());
    if (opt.getCutLoops()) stages.add(new LoopCutter());
    if (opt.getDesugarCalls()) stages.add(new CallDesugarer());
    if (opt.getDesugarHavoc()) stages.add(new HavocDesugarer());
    if (opt.getDesugarSpec()) stages.add(new SpecDesugarer());
    if (opt.getPassivate()) {
      switch (opt.getPassivatorOpt()) {
        case OPTIM: stages.add(new Passivator()); break;
        default: stages.add(new Passificator()); break;
      }
    }
    if (opt.getDoVcGen()) {
      VcGenerator vcgen = new VcGenerator();
      vcgen.initialize(opt);
      stages.add(vcgen);
    }

    // Initialize other stuff.
    prettyPrinter.boogieVersion(opt.getBoogieVersionOpt());
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
      return false;
    }
    return true;
  }

  private void dumpState(String stageName) {
    if (!opt.isDumpIntermediateStagesSet()) return;
    log.say(
        LogCategories.MAIN,
        LogLevel.INFO,
        "Dump after stage " + stageName + ".");
    File dir = new File(opt.getDumpIntermediateStages(), stageName);
    dir.mkdirs();

    // dump boogie
    try {
      PrintWriter bw = new PrintWriter(new File(dir, boogie.fileName));
      prettyPrinter.writer(bw);
      prettyPrinter.process(boogie, tc);
      bw.flush();
    } catch (FileNotFoundException e) {
      assert false : "PrintWriter should create the file.";
    }

    // dump symbol table
    try {
      SymbolTable st = tc.getST();
      PrintWriter stw = new PrintWriter(new File(dir, "symbols.txt"));
      printSymbols(stw, "function", st.funcs, nameOfFunctionDecl);
      printSymbols(stw, "identifier", st.ids, nameOfVar);
      printSymbols(stw, "procedure", st.procs, nameOfProcedure);
      printSymbols(stw, "type", st.types, nameOfType);
      printSymbols(stw, "typevar", st.typeVars,nameOfAtomId);
      stw.flush();
    } catch (FileNotFoundException e) {
      assert false : "PrintWriter should create the file.";
    }

    // dump flowgraphs
    flowGraphDumper.directory(dir);
    flowGraphDumper.process(boogie, tc);
  }

  private <U extends Ast, D extends Ast> void printSymbols(
      final PrintWriter w,
      final String t,
      final UsageToDefMap<U, D> map,
      final Function<D, String> toString
  ) {
    map.iterDef(new Closure<D>() {
      @Override public void go(D d) {
        w.println(t + " " + toString.apply(d));
        w.println("  definition at " + d.loc());
        w.print("  usages at");
        for (U u : map.usages(d)) w.print(" " + u.loc());
        w.println();
      }});    
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
