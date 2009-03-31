package freeboogie;

import java.io.*;
import java.util.logging.*;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CommonTokenStream;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.backend.*;
import freeboogie.dumpers.FlowGraphDumper;
import freeboogie.parser.FbLexer;
import freeboogie.parser.FbParser;
import freeboogie.tc.*;
import freeboogie.util.*;
import freeboogie.vcgen.*;

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
  private static Logger log = Logger.getLogger("freeboogie"); 
  public static Options opt;
  
  /**
   * The main entry point of the application.
   * @param args the command line arguments
   */
  public static void main(String[] args) { new Main().run(args); }

  private PrintWriter pwriter;
  private PrettyPrinter pp;
  private FlowGraphDumper fgd;
  private TcInterface tc;
  private Program program; // the program being processed
    // TODO(rgrig): add a "Program process(Program)" method

  private VcGenerator<SmtTerm> vcgen;
  private Prover<SmtTerm> prover;


  public Main() {
    opt = new Options();
    opt.regBool("-log", "log events to ./freeboogie.log");
    opt.regBool("-pp", "pretty print");
    opt.regBool("-pst", "print symbol table");
    opt.regBool("-pfg", "print flow graphs");
    opt.regBool("-pass", "passivate");
    opt.regBool("-passify", "passify");
    opt.regBool("-dspec", "desugar specs");
    opt.regBool("-dcall", "desugar calls");
    opt.regBool("-dhavoc", "desugar havoc");
    opt.regBool("-dloop", "havoc loop variables at loop entry");
    opt.regBool("-cut", "cut loops by removing back-edges");
    opt.regBool("-dmap", "desugar maps");
    opt.regBool("-old", "accept old constructs");
    opt.regBool("-win", "windows mode");
    opt.regBool("-verify", "do everything");
    opt.regBool("-removesharing", "remove sharing in vc");
    opt.regBool("-stats", "Prints some statistics");
    opt.regBool("-wp", "weakest precondition");
    opt.regBool("-wpno", "weakest precondition with no tricks");
    opt.regInt("-v", 4, "verbosity level: 0, 1, 2, 3, 4");
    pwriter = new PrintWriter(System.out);
    pp = new PrettyPrinter(pwriter);
    fgd = new FlowGraphDumper();
    vcgen = new VcGenerator<SmtTerm>(new DeSharifier());
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
    st.typeVars.iterDef(new Printer<UserType, AtomId>("type variable", st.typeVars,
      new ClosureR<AtomId, String>() {
        @Override public String go(AtomId a) {
          return a.getId();
      }}));
  }

  private void passivate(boolean isVerbose) {
    Passivator p = new Passivator(isVerbose);
    program = p.process(program, tc);
  }
  private void passify(boolean isVerbose) {
    Passificator p = new Passificator(tc, isVerbose);
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
    ACalculus<SmtTerm> calculus;
    if (opt.boolVal("-wp")) {
      calculus = new WeakestPrecondition<SmtTerm>(tc);
    }
    else if (opt.boolVal("-wpno")) {
      calculus = new WeakestPrecondition<SmtTerm>(tc);
      ((WeakestPrecondition<SmtTerm>)calculus).setAssertAsAssertAssume(false);
    }
    else {
      calculus = new StrongestPostcondition<SmtTerm>(tc);
    }
    
    if (prover == null) {
      if (opt.boolVal("-win"))
        prover = new SimplifyProver(new String[]{"Z3.exe", "/si"});
      else
        prover = new SimplifyProver(new String[]{"z3", "-si"});
//prover = new YesSmtProver();
      vcgen.initialize(prover, calculus);
    }
    program = new Program(vcgen.process(program.ast, tc), program.fileName);

    boolean removeSharing = opt.boolVal("-removesharing");
    
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
          vcgen.verify(impl, removeSharing)? " OK" : "NOK",
          impl.getSig().getName(),
          impl.getSig().loc());
        d = impl.getTail();
      }
    }
  }

  public void run(String[] args) {
    // parse command line arguments
    opt.parse(args);
    Err.setVerbosity(opt.intVal("-v"));
    tc = opt.boolVal("-old") ? new ForgivingTc() : new TypeChecker();
    
    // prepare logging
    log.setLevel(Level.ALL);
    log.setUseParentHandlers(false); // the root logger sends >=INFO to console
    try {
      FileHandler logh = new FileHandler("freeboogie.log");
      logh.setFormatter(new OneLineLogFormatter());
      log.addHandler(logh);
      if (opt.boolVal("-log")) log.setLevel(Level.ALL);
    } catch (IOException e) {
      Err.warning("Can't create log file. Nevermind.");
    }
    
    // process files one by one
    for (String file : opt.otherArgs()) {
      if (opt.intVal("-v") > 0) {
        System.out.println("Processing file " + file);
      }
      try {
        // parse an input file
        FbLexer lexer = new FbLexer(new ANTLRFileStream(file));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FbParser parser = new FbParser(tokens);
        parser.fileName = file;
        program = new Program(parser.program(), file);
        if (program.ast == null) 
          continue; // errors while parsing or empty file
        
        // do what we are asked to do with this file
        if (FbError.reportAll(tc.process(program.ast))) continue;
        program = new Program(tc.getAST(), program.fileName);
        if (opt.boolVal("-pst")) printSymbolTable();
        if (!opt.boolVal("-verify")) {
          if (opt.boolVal("-dloop")) makeHavoc();
          if (opt.boolVal("-cut")) cutLoops();
          if (opt.boolVal("-dcall")) desugarCalls();
          if (opt.boolVal("-dhavoc")) desugarHavoc();
          if (opt.boolVal("-dspec")) desugarSpecs();
          if (opt.boolVal("-pass")) passivate(opt.boolVal("-stats"));
          if (opt.boolVal("-passify")) passify(opt.boolVal("-stats"));
          if (opt.boolVal("-dmap")) removeMaps();
        } else verify();
        if (opt.boolVal("-pfg")) fgd.process(program.ast, tc);
        if (opt.boolVal("-pp")) program.ast.eval(pp);
      } catch (FileNotFoundException e) {
        Err.error("I couldn't read from " + file + ". Nevermind.");
      } catch (ProverException e) {
        e.printStackTrace();
        Err.error("Bad prover! I'll kill it and make a new one.");
        prover.terminate();
        prover = null;
      } catch (Throwable e) {
        Err.error(e.getMessage());
        e.printStackTrace();
        Err.error("Unexpected error while processing " + file);
      } finally {
        pwriter.flush();
      }
    }
  }
}
