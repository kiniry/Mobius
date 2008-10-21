package freeboogie;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.List;
import java.util.logging.*;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CommonTokenStream;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.dumpers.FlowGraphDumper;
import freeboogie.parser.FbLexer;
import freeboogie.parser.FbParser;
import freeboogie.tc.*;
import freeboogie.util.Closure;
import freeboogie.util.ClosureR;
import freeboogie.util.Err;
import freeboogie.vcgen.BlockSplitter;

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

  /**
   * The main entry point of the application.
   * @param args the command line arguments
   */
  public static void main(String[] args) { new Main().run(args); }

  private Options opt;
  private PrintWriter pwriter;
  private PrettyPrinter pp;
  private FlowGraphDumper fgd;
  private TcInterface tc;
  private Declaration ast;

  public Main() {
    opt = new Options();
    opt.regBool("-pp", "pretty print");
    opt.regBool("-pst", "print symbol table");
    opt.regBool("-pfg", "print flow graphs");
    opt.regBool("-old", "accept old constructs");
    opt.regBool("-sb", "split blocks so they contain one command");
    opt.regBool("-pvc", "print verification condition");
    opt.regInt("-v", 4, "verbosity level: 0, 1, 2, 3, 4");
    pwriter = new PrintWriter(System.out);
    pp = new PrettyPrinter(pwriter);
    fgd = new FlowGraphDumper();
  }

  public void printSymbolTable() {
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

  private void chopBlocks() {
    BlockSplitter bs = new BlockSplitter();
    ast = (Declaration)ast.eval(bs);
    tc.process(ast);
  }

  public void run(String[] args) {
    // prepare logging
    try {
      FileHandler logh = new FileHandler("freeboogie.log");
      logh.setFormatter(new SimpleFormatter());
      log.addHandler(logh);
      //log.setLevel(Level.OFF);
      log.setLevel(Level.ALL); // TODO Control using a properties file.
      log.setUseParentHandlers(false); // the 'root' logger sends >=INFO to console
    } catch (IOException e) {
      Err.warning("Can't create log file. Nevermind.");
      log.setLevel(Level.OFF);
    }
    
    // parse command line arguments
    opt.parse(args);
    Err.setVerbosity(opt.intVal("-v"));
    tc = opt.boolVal("-old") ? new ForgivingTc() : new TypeChecker();
    
    // process files one by one
    for (String file : opt.otherArgs()) {
      try {
        // parse an input file
        FbLexer lexer = new FbLexer(new ANTLRFileStream(file));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FbParser parser = new FbParser(tokens);
        parser.fileName = file;
        ast = parser.program();
        if (ast == null) continue; // errors while parsing or empty file
        
        // do what we are asked to do with this file
        if (opt.boolVal("-sb")) chopBlocks();
        if (FbError.reportAll(tc.process(ast))) continue;
        ast = tc.getAST();
        if (opt.boolVal("-pp")) ast.eval(pp);
        if (opt.boolVal("-pst")) printSymbolTable();
        if (opt.boolVal("-pfg")) fgd.process(ast, tc);
      } catch (FileNotFoundException e) {
        Err.error("I couldn't read from " + file + ". Nevermind.");
      } catch (Exception e) {
        Err.error(e.getMessage());
        e.printStackTrace();
        Err.error("Unexpected error while processing " + file);
      } finally {
        pwriter.flush();
      }
    }
  }
}
