package freeboogie.vcgen;

import java.io.PrintWriter;
import java.util.*;
import java.util.logging.Logger;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.util.Err;
import freeboogie.tc.FbError;
import freeboogie.tc.TcInterface;

/**
 * Desugar call commands into a sequence of asserts, havocs, and assumes.
 *
 * Given:
 * <pre>
 * var Heap : [ref]int;
 * procedure Calee(x : int) return (y : int);
 *   requires P(x);
 *   modifies Heap;
 *   ensures Q(x, y);
 * </pre>
 *
 * The code
 * <pre>
 * implementation Caller(v : int) returns (w : int) {
 * entry:
 *   call w := Callee(v);
 * }
 * </pre>
 * becomes
 * <pre>
 * implementation Caller(v : int) returns (w : int) {
 * entry:
 *   assert P(v);
 *   havoc Heap;
 *   assume Q(v, w);
 * }
 * </pre>
 *
 * NOTE: Free modifies are ignored.
 */
public class CallDesugarer extends Transformer {
  private static final Logger log = Logger.getLogger("freeboogie.vcgen");

  private TcInterface tc;

  private HashMap<VariableDecl, Expr> toSubstitute;
  private ArrayList<Expr> preconditions;
  private ArrayList<Expr> postconditions;
  private ArrayList<Identifiers> havocs;
  private ArrayList<Command> equivCmds;

  public CallDesugarer() {
    toSubstitute = new HashMap<VariableDecl, Expr>(23);
    preconditions = new ArrayList<Expr>(23);
    postconditions = new ArrayList<Expr>(23);
    havocs = new ArrayList<Identifiers>(23);
    equivCmds = new ArrayList<Command>(23);
  }

  public Declaration process(Declaration ast, TcInterface tc) {
    this.tc = tc;
    ast = (Declaration)ast.eval(this);
    List<FbError> errors = tc.process(ast);
    if (!errors.isEmpty()) {
      FbError.reportAll(errors);
      PrintWriter pw = new PrintWriter(System.out);
      PrettyPrinter pp = new PrettyPrinter(pw);
      ast.eval(pp);
      pw.flush();
      Err.fatal("INTERNAL ERROR: CallDesugarer produced invalid Boogie.");
    }
    return tc.getAST();
  }

  // === transformer methods ===
  
  @Override
  public Block eval(Block block, String name, Command cmd, Identifiers succ, Block tail) {
    equivCmds.clear();
    Block newTail = tail == null? null : (Block)tail.eval(this);
    Command newCmd = cmd == null? null : (Command)cmd.eval(this);
    if (newCmd == null) {
      // replace with a sequence of blocks built from equivCmds
      // TODO
    } else {
      assert newCmd == cmd;
      if (newTail != tail)
        block = Block.mk(name, newCmd, succ, newTail);
    }
    return block;
  }

  @Override
  public Command eval(CallCmd callCmd, String procedure, TupleType types, Identifiers results, Exprs args) {
    toSubstitute.clear();
    preconditions.clear();
    postconditions.clear();
    havocs.clear();
    equivCmds.clear();
    Procedure p = tc.getST().procs.def(callCmd);
    Signature sig = p.getSig();
    VariableDecl rv = (VariableDecl)sig.getResults();
    while (rv != null) {
      toSubstitute.put(rv, results.getId());
      rv = (VariableDecl)rv.getTail();
      results = results.getTail();
    }
    VariableDecl av = (VariableDecl)sig.getArgs();
    while (av != null) {
      toSubstitute.put(av, args.getExpr());
      av = (VariableDecl)av.getTail();
      args = args.getTail();
    }
    Specification spec = p.getSpec();
    while (spec != null) {
      Expr se = (Expr)spec.getExpr().clone().eval(this);
      switch (spec.getType()) {
      case REQUIRES:  
        preconditions.add(se); break;
      case ENSURES:
        postconditions.add(se); break;
      case MODIFIES:
        if (!spec.getFree()) {
          Identifiers ids = null;
          Exprs e = (Exprs)se;
          while (e != null) {
            ids = Identifiers.mk((AtomId)e.getExpr(), ids, e.getExpr().loc());
            e = e.getTail();
          }
          havocs.add(ids); 
        }
        break;
      default:
        assert false;
      }
      spec = spec.getTail();
    }
    for (Expr pre : preconditions) {
      equivCmds.add(AssertAssumeCmd.mk(
        AssertAssumeCmd.CmdType.ASSERT,
        null,
        pre,
        callCmd.loc()));
    }
    for (Identifiers h : havocs)
      equivCmds.add(HavocCmd.mk(h, callCmd.loc()));
    for (Expr post : postconditions) {
      equivCmds.add(AssertAssumeCmd.mk(
        AssertAssumeCmd.CmdType.ASSUME,
        null,
        post,
        callCmd.loc()));
    }
    toSubstitute.clear();
    return null;
  }
  
  // TODO: when visiting AtomId apply toSubstitute
}
