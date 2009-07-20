package freeboogie;

import java.io.*;
import java.util.logging.*;

import genericutils.*;
import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;
import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CommonTokenStream;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.astutil.Boogie2Printer;
import freeboogie.backend.*;
import freeboogie.cli.FbCliOptionsInterface;
import freeboogie.cli.FbCliParser;
import freeboogie.cli.FbCliUtil;
import freeboogie.dumpers.FlowGraphDumper;
import freeboogie.parser.FbLexer;
import freeboogie.parser.FbParser;
import freeboogie.tc.*;
import freeboogie.vcgen.*;

import static freeboogie.cli.FbCliOptionsInterface.ReportLevel;

/**
 * Used to print information in the symbol table.
 * (Java is incredibly verbose for this kind of stuff.)
 *
 * @author rgrig 
 * @param <U> the usage type
 * @param <D> the definition type
 */
class Printer<U extends Ast, D extends Ast> extends Closure<D> {
  private String name;
  private UsageToDefMap<U, D> map;
  private ClosureR<D, String> nameGetter;
  
  /**
   * Constructs a printer.
   * @param n the type of element that is printed
   * @param m the usage-def map
   * @param g a function that gets a user readable name from a definition
   */
  public Printer(String n, UsageToDefMap<U, D> m, ClosureR<D, String> g) {
    name = n; map = m; nameGetter = g;
  }

  @Override
  public void go(D t) {
    System.out.println(name + " " + nameGetter.go(t));
    System.out.println("  definition at " + t.loc());
    System.out.print("  usages at");
    for (U u : map.usages(t))
      System.out.print(" " + u.loc());
    System.out.println();
  }
}

/**
 * The main entry point of the application.
 *
 * @author rgrig 
 */
public class Main {
  // NOTE: the long names are temporary: this file and java.util.logging
  // will go away soon
  private static java.util.logging.Logger log = 
    java.util.logging.Logger.getLogger("freeboogie"); 
  public static FbCliOptionsInterface opt;
  
  /**
   * The main entry point of the application.
   * @param args the command line arguments
   */
  public static void main(String[] args) throws Throwable { 
    new Main().run(args); 
  }

  private PrintWriter pwriter;
  private PrettyPrinter pp;
  private Boogie2Printer pb2;
  private FlowGraphDumper fgd;
  private TcInterface tc;
  private Program program; // the program being processed
    // TODO(rgrig): add a "Program process(Program)" method

  private VcGenerator<SmtTerm> vcgen;
  private Prover<SmtTerm> prover;


  public Main() {
    pwriter = new PrintWriter(System.out);
    pp = new PrettyPrinter(pwriter);
    pb2 = new Boogie2Printer(pwriter);
    fgd = new FlowGraphDumper();
    vcgen = new VcGenerator<SmtTerm>();
  }

  private void printSymbolTable() {
    SymbolTable st = tc.getST();
    st.funcs.iterDef(new Printer<AtomFun, Function>("function", st.funcs,
      new ClosureR<Function, String>() {
        @Override public String go(Function p) {
          return p.getSig().getName();
        }}));
    st.ids.iterDef(new Printer<AtomId, Declaration>("identifier", st.ids,
      new ClosureR<Declaration, String>() {
        @Override public String go(Declaration p) {
          if (p instanceof VariableDecl) 
            return ((VariableDecl)p).getName();
          else if (p instanceof ConstDecl)
            return ((ConstDecl)p).getId();
          assert false;
          return null; // dumb compiler
        }}));
    st.procs.iterDef(new Printer<CallCmd, Procedure>("procedure", st.procs,
      new ClosureR<Procedure, String>() {
        @Override public String go(Procedure p) {
          return p.getSig().getName();
        }}));
    st.types.iterDef(new Printer<UserType, TypeDecl>("type", st.types,
      new ClosureR<TypeDecl, String>() {
        @Override public String go(TypeDecl p) {
          return p.getName();
      }}));
    st.typeVars.iterDef(
      new Printer<UserType, AtomId>("type variable", st.typeVars,
        new ClosureR<AtomId, String>() {
          @Override public String go(AtomId a) {
            return a.getId();
        }}));
  }
  private void spgCheck() {
    TtspRecognizer.check(program, tc);
  }
  private void passivate() {
    Passivator p = new Passivator();
    program = p.process(program, tc);
  }
  private void passify() {
    Passificator p = new Passificator(tc);
    program = p.process(program);
  }
  
  private void removeMaps() {
    MapRemover mr = new MapRemover();
    program = new Program(mr.process(program.ast, tc), program.fileName);
  }

  private void desugarSpecs() {
    SpecDesugarer d = new SpecDesugarer();
    program = new Program(d.process(program.ast, tc), program.fileName);
  }

  private void desugarCalls() {
    CallDesugarer d = new CallDesugarer();
    program = new Program(d.process(program.ast, tc), program.fileName);
  }

  private void makeHavoc() {
    HavocMaker hm = new HavocMaker();
    program = new Program(hm.process(program.ast, tc), program.fileName);
  }

  private void cutLoops() {
    LoopCutter c = new LoopCutter();
    program = new Program(c.process(program.ast, tc), program.fileName);
  }

  private void desugarHavoc() {
    HavocDesugarer d = new HavocDesugarer();
    program = new Program(d.process(program.ast, tc), program.fileName);
  }

  private void verify() throws ProverException {
    ACalculus<SmtTerm> calculus = null;
    switch (opt.getVcMethod()) {
    case WP: 
      calculus = new WeakestPrecondition<SmtTerm>(tc); 
      break;
    case WPNO: 
      calculus = new WeakestPrecondition<SmtTerm>(tc);
      ((WeakestPrecondition<SmtTerm>)calculus).setAssertAsAssertAssume(false);
      break;
    case SP:
      calculus = new StrongestPostcondition<SmtTerm>(tc);
      break;
    default:
      assert false : "Internal error";
    }
    
    if (prover == null) {
      switch (opt.getProver()) {
      case SIMPLIFY: 
        prover = new SimplifyProver(opt.getProverCommandLine().split("\\s+"));
        break;
      case YESMAN:
        prover = new YesSmtProver();
      }
      vcgen.initialize(prover, calculus);
    }
    program = new Program(vcgen.process(program.ast, tc), program.fileName);

    // This is ugly. Perhaps put this in a visitor that also knows
    // how to filter which implementations to check.
    Declaration d = program.ast;
    while (d != null) {
      if (d instanceof TypeDecl) d = ((TypeDecl)d).getTail();
      else if (d instanceof ConstDecl) d = ((ConstDecl)d).getTail();
      else if (d instanceof Axiom) d = ((Axiom)d).getTail();
      else if (d instanceof Function) d = ((Function)d).getTail();
      else if (d instanceof VariableDecl) d = ((VariableDecl)d).getTail();
      else if (d instanceof Procedure) d = ((Procedure)d).getTail();
      else {
        Implementation impl = (Implementation)d;
        System.out.printf(
          "%s: %s (%s)\n",
          vcgen.verify(impl)? " OK" : "NOK",
          impl.getSig().getName(),
          impl.getSig().loc());
        d = impl.getTail();
      }
    }
  }

  public void badCli() {
    System.err.println("I don't understand what you want. Try --help.");
    System.exit(1);
  }

  public void run(String[] args) 
  throws InvalidOptionPropertyValueException, AutomatonException {
/*
    // parse command line arguments
    FbCliParser cliParser = new FbCliParser();
    try { if (!cliParser.parse(args)) badCli(); }
    catch (InvalidOptionValueException e) { badCli(); }
    opt = cliParser.getOptionStore();
    if (opt.isHelpSet()) {
      FbCliUtil.printUsage();
      return;
    }
    if (opt.getFiles().isEmpty()) {
      System.out.println("Nothing to do. Try --help.");
      return;
    }

    Err.setVerbosity(4); // TODO: take from the command line 
    tc = opt.isBackwardCompatibleSet()? new ForgivingTc() : new TypeChecker();
    
    // prepare logging
    log.setUseParentHandlers(false); // the root logger sends >=INFO to console
    if (opt.isLogFileSet()) {
      try {
        FileHandler logh = new FileHandler(opt.getLogFile().getPath(), true);
        logh.setFormatter(new OneLineLogFormatter());
        log.addHandler(logh);
      } catch (IOException e) {
        Err.warning("Can't create log file. Nevermind.");
      }
    }
    if (opt.isLogLevelSet()) {
      switch (opt.getLogLevel()) {
      case SEVERE: log.setLevel(Level.SEVERE); break;
      case WARNING: log.setLevel(Level.WARNING); break;
      case INFO: log.setLevel(Level.INFO); break;
      default: assert false : "Internal error";
      }
    }
    
    // process files one by one
    for (File file : opt.getFiles()) {
      if (ReportLevel.NORMAL.compareTo(opt.getReportLevel()) >= 0) {
        System.out.println("Processing file " + file);
      }
      try {
        // parse an input file
        FbLexer lexer = new FbLexer(new ANTLRFileStream(file.getPath()));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FbParser parser = new FbParser(tokens);
        parser.fileName = file.getName();
        program = new Program(parser.program(), file.getName());
        if (program.ast == null) 
          continue; // errors while parsing or empty file
        
        // do what we are asked to do with this file
        if (FbError.reportAll(tc.process(program.ast))) continue;
        program = new Program(tc.getAST(), program.fileName);
        if (opt.isPrintSymbolTableSet()) printSymbolTable();
        if (!opt.isVerifySet()) {
          if (opt.isHavocLoopVariablesSet()) makeHavoc();
          if (opt.isCutLoopsSet()) cutLoops();
          if (opt.isDesugarCallsSet()) desugarCalls();
          if (opt.isDesugarHavocSet()) desugarHavoc();
          if (opt.isDesugarSpecsSet()) desugarSpecs();
          if (opt.isSeriesParallelCheckSet()) spgCheck();
          switch (opt.getPassivate()) {
          case OPTIM: passivate(); break;
          case ESCJAVA: passify(); break;
          default: // do nothing
          }
          if (opt.isDesugarMapsSet()) removeMaps();
        } else verify();
        if (opt.isPrintFlowgraphsSet()) fgd.process(program.ast, tc);
        if (opt.isPrettyPrintSet()) program.ast.eval(pp);
        if (opt.isPrintBoogie2Set()) pb2.process(program.ast);
      } catch (FileNotFoundException e) {
        Err.error("I couldn't read from " + file + ". Nevermind.");
      } catch (ProverException e) {
        e.printStackTrace();
        Err.error("Bad prover! I'll kill it and make a new one.");
        //Terminate prover
//        prover.terminate();
//        prover = null;
      } catch (Throwable e) {
        Err.error(e.getMessage());
        e.printStackTrace();
        Err.error("Unexpected error while processing " + file);
      } finally {
        //Remove after testing completed.
        if (prover != null) {
          prover.terminate();
          prover = null;
        }
        pwriter.flush();
      }
    }
*/
  }
}
