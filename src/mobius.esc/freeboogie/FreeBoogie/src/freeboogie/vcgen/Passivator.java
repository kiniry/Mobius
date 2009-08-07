package freeboogie.vcgen;

import java.io.PrintWriter;
import java.util.*;
import java.util.logging.Logger;

import genericutils.*;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.tc.*;
import freeboogie.vcgen.ABasicPassifier.Environment;

/**
 * Gets rid of assignments and "old" expressions by introducing 
 * new variables. We assume that
 *   (1) specs are desugared,
 *   (2) calls are desugared,
 *   (3) havocs are desugared,
 *   (4) the flowgraphs are computed and have no cycles.
 *
 * Each variable X is transformed into a sequence of variables
 * X, X_1, X_2, ... Each command has a read index r and a write
 * index w (for each variable), meaning that reads from X will be
 * replaced by reads from X_r and a write to X is replaced by a
 * write to X_w.
 *
 * We have:
 *   r(n) = max_{m BEFORE n} w(m)
 *   w(n) = 1 + r(n)   if n writes to X
 *   w(n) = r(n)       otherwise
 *
 * Copy operations (assumes) need to be inserted when the value
 * written by a node is not the same as the one read by one of
 * its successors (according the the scheme above).
 *
 * The "old()" is simply stripped.
 *
 * This algorithm minimizes the number of variables (think
 * coloring of comparison graphs) but not the number of copy
 * operations.
 *
 * TODO Introduce new variable declarations
 * TODO Change the out parameters of implementations to refer to the last version
 *
 * @author rgrig
 */
public class Passivator extends Transformer {
  // used mainly for debugging
  private static final Logger log = Logger.getLogger("freeboogie.vcgen");

  private String fileName;
  private HashMap<VariableDecl, HashMap<Block, Integer>> readIdx;
  private HashMap<VariableDecl, HashMap<Block, Integer>> writeIdx;
  private HashMap<VariableDecl, Integer> newVarsCnt;
  private HashMap<VariableDecl, Integer> toReport;
  private HashMap<Command, HashSet<VariableDecl>> commandWs;
  private ReadWriteSetFinder rwsf;

  private VariableDecl currentVar;
  private HashMap<Block, Integer> currentReadIdxCache;
  private HashMap<Block, Integer> currentWriteIdxCache;
  private SimpleGraph<Block> currentFG;
  private Block currentBlock;
  private HashSet<VariableDecl> allWritten; // by the current implementation
  private Declaration newLocals;

  private Deque<Boolean> context; // true = write, false = read
  private int belowOld;

  // === public interface ===
  
  public Program process(Program program, TcInterface tc) {
    fileName = program.fileName;
    return new Program(process(program.ast, tc), fileName);
  }
  
  @Override
  public Declaration process(Declaration ast, TcInterface tc) {
    this.tc = tc;
    readIdx = new LinkedHashMap<VariableDecl, HashMap<Block, Integer>>();
    writeIdx = new LinkedHashMap<VariableDecl, HashMap<Block, Integer>>();
    newVarsCnt = new LinkedHashMap<VariableDecl, Integer>();
    toReport = new LinkedHashMap<VariableDecl, Integer>();
    commandWs = new LinkedHashMap<Command, HashSet<VariableDecl>>();
    rwsf = new ReadWriteSetFinder(tc.getST());
    ast = (Declaration)ast.eval(this);
    for (Map.Entry<VariableDecl, Integer> e : newVarsCnt.entrySet()) {
      for (int i = 1; i <= e.getValue(); ++i) {
        Identifiers ntv = e.getKey().getTypeArgs();
        if (ntv != null) ntv = ntv.clone();
        ast = VariableDecl.mk(
          null,
          e.getKey().getName()+"$$"+i, 
          TypeUtils.stripDep(e.getKey().getType()).clone(), 
          ntv, 
          ast);
      }
    }
    if (false) { // TODO log-categ
      System.out.print(Environment.mapToString(toReport));
    }
    if (!tc.process(ast).isEmpty()) {
      PrintWriter pw = new PrintWriter(System.out);
      PrettyPrinter pp = new PrettyPrinter();
      pp.writer(pw);
      ast.eval(pp);
      pw.flush();
      Err.internal("Passivator produced invalid Boogie.");
    }
    return tc.getAST();
  }

  // === (block) transformers ===

  @Override
  public Implementation eval(
    Implementation implementation,
    Attribute attr, 
    Signature sig,
    Body body,
    Declaration tail
  ) {
    currentFG = tc.getFlowGraph(implementation);
    if (currentFG.hasCycle()) {
      Err.warning("" + implementation.loc() + ": Implementation " + 
        sig.getName() + " has cycles. I'm not passivating it.");
      if (tail != null) tail = (Declaration)tail.eval(this);
      return Implementation.mk(attr, sig, body, tail);
    }
    
    // collect all variables that are assigned to
    Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> rwIds = 
      implementation.eval(rwsf);
    allWritten = new LinkedHashSet<VariableDecl>();
    for (VariableDecl vd : rwIds.second) allWritten.add(vd);

    // figure out read and write indexes
    for (VariableDecl vd : allWritten) {
      currentVar = vd;
      currentReadIdxCache = new LinkedHashMap<Block, Integer>();
      currentWriteIdxCache = new LinkedHashMap<Block, Integer>();
      readIdx.put(vd, currentReadIdxCache);
      writeIdx.put(vd, currentWriteIdxCache);
      currentFG.iterNode(new Closure<Block>() {
        @Override public void go(Block b) {
          compReadIdx(b); compWriteIdx(b);
        }
      });
    }

    // transform the body
    context = new ArrayDeque<Boolean>();
    context.addFirst(false);
    currentBlock = null;
    belowOld = 0;

    body = (Body)body.eval(this);
    context = null;
    currentFG = null;

    // process out parameters
    newLocals = body.getVars();

    sig = Signature.mk(
      sig.getName(), 
      sig.getTypeArgs(),
      sig.getArgs(),
      newResults((VariableDecl)sig.getResults()),
      sig.loc());
    body = Body.mk(newLocals, body.getBlocks());

    // process the rest of the program
    if (tail != null) tail = (Declaration)tail.eval(this);
    return Implementation.mk(attr, sig, body, tail);
  }


  // === workers ===

  private int compReadIdx(Block b) {
    if (currentReadIdxCache.containsKey(b))
      return currentReadIdxCache.get(b);
    int ri = 0;
    for (Block pre : currentFG.from(b))
      ri = Math.max(ri, compWriteIdx(pre));
    currentReadIdxCache.put(b, ri);
    return ri;
  }

  private int compWriteIdx(Block b) {
    if (currentWriteIdxCache.containsKey(b))
      return currentWriteIdxCache.get(b);
    int wi = compReadIdx(b);
    if (b.getCmd() != null) {
      HashSet<VariableDecl> ws = commandWs.get(b.getCmd());
      if (ws == null) {
        ws = new LinkedHashSet<VariableDecl>();
        for (VariableDecl vd : rwsf.get(b.getCmd()).second) ws.add(vd);
        commandWs.put(b.getCmd(), ws);
      }
      if (ws.contains(currentVar)) ++wi;
    }
    currentWriteIdxCache.put(b, wi);
    int owi = newVarsCnt.containsKey(currentVar) ? newVarsCnt.get(currentVar) : 0;
    newVarsCnt.put(currentVar, Math.max(owi, wi));
    return wi;
  }


  // === visitors ===
  @Override
  public Block eval(Block block, String name, Command cmd, Identifiers succ, Block tail) {
    // first process the rest
    Block newTail = tail == null? null : (Block)tail.eval(this);

    currentBlock = block;
    // change variable occurrences in the command of this block
    Command newCmd = cmd == null? null : (Command)cmd.eval(this);

    /* Compute the successors, perhaps introducing extra blocks for
     * copy operations.
     */
    Identifiers newSucc = null;
    for (Block s : currentFG.to(block)) {
      Block ss = s; // new successor
      for (VariableDecl v : allWritten) {
        int ri = readIdx.get(v).get(s);
        int wi = writeIdx.get(v).get(block);
        if (ri == wi) continue;
        // TODO: Perhaps I need to specify some type variables?
        ss = newTail = Block.mk(
          Id.get("copy"),
          AssertAssumeCmd.mk(
            AssertAssumeCmd.CmdType.ASSUME,
            null,
            BinaryOp.mk(
              BinaryOp.Op.EQ,
              AtomId.mk(v.getName() + (ri > 0? "$$" + ri : ""), null),
              AtomId.mk(v.getName() + (wi > 0? "$$" + wi : ""), null))),
          Identifiers.mk(
            AtomId.mk(ss.getName(), null),
            null),
          newTail,
          block.loc());
      }
      newSucc = Identifiers.mk(AtomId.mk(ss.getName(), null), newSucc);
    }
    currentBlock = null;

    if (newCmd != cmd || newTail != tail)
      block = Block.mk(name, newCmd, newSucc, newTail, block.loc());
    return block;
  }

  public AssertAssumeCmd eval(AssertAssumeCmd assertAssumeCmd, AssertAssumeCmd.CmdType type, Identifiers typeVars, Expr expr) {
    Expr newExpr = (Expr)expr.eval(this);
    if (newExpr != expr)
      return AssertAssumeCmd.mk(type, typeVars, newExpr);
    return assertAssumeCmd;
  }

  @Override
  public AssertAssumeCmd eval(AssignmentCmd assignmentCmd, AtomId lhs, Expr rhs) {
    AssertAssumeCmd result = null;
    Expr value = (Expr)rhs.eval(this);
    VariableDecl vd = (VariableDecl)tc.getST().ids.def(lhs);
    result = AssertAssumeCmd.mk(AssertAssumeCmd.CmdType.ASSUME, null,
        BinaryOp.mk(BinaryOp.Op.EQ,
          AtomId.mk(
            lhs.getId()+"$$"+getIdx(writeIdx, vd), 
            lhs.getTypes(), 
            lhs.loc()),
          value));
    return result;
  }

  @Override
  public Expr eval(AtomOld atomOld, Expr e) {
    ++belowOld;
    e = (Expr)e.eval(this);
    --belowOld;
    return e;
  }

  @Override
  public AtomId eval(AtomId atomId, String id, TupleType types) {
    if (currentBlock == null) return atomId;
    Declaration d = tc.getST().ids.def(atomId);
    if (!(d instanceof VariableDecl)) return atomId;
    VariableDecl vd = (VariableDecl)d;
    int idx = context.getFirst() ? getIdx(writeIdx, vd) : getIdx(readIdx, vd);
    if (idx == 0) return atomId;
    return AtomId.mk(id + "$$" + idx, types, atomId.loc());
  }

  @Override
  public VariableDecl eval(
    VariableDecl variableDecl,
    Attribute attr,
    String name,
    Type type,
    Identifiers typeArgs,
    Declaration tail
  ) {
    int last = newVarsCnt.containsKey(variableDecl) ? newVarsCnt.get(variableDecl) : 0;
    if (false) { // TODO log-categ
      toReport.put(variableDecl, last);
    }
    newVarsCnt.remove(variableDecl);
    Declaration newTail = tail == null? null : (Declaration)tail.eval(this);
    if (newTail != tail) {
      variableDecl = VariableDecl.mk(
        null,
        name, 
        TypeUtils.stripDep(type).clone(), 
        typeArgs == null? null : typeArgs.clone(),
        newTail, 
        variableDecl.loc());
    }
    for (int i = 1; i <= last; ++i) {
      variableDecl = VariableDecl.mk(
        null,
        name+"$$"+i, 
        TypeUtils.stripDep(type).clone(), 
        typeArgs == null? null : typeArgs.clone(), 
        variableDecl);
    }
    return variableDecl;
  }

  // === helpers ===
  private int getIdx(HashMap<VariableDecl, HashMap<Block, Integer> > cache, VariableDecl vd) {
    Map<Block, Integer> m = cache.get(vd);
    if (m == null || belowOld > 0 || currentBlock == null) 
      return 0; // this variable is never written to
    Integer idx = m.get(currentBlock);
    return idx == null? 0 : idx;
  }

  private VariableDecl newResults(VariableDecl old) {
    if (old == null) return null;
    Integer last = newVarsCnt.get(old);
    if (false) { // TODO log-categ
      toReport.put(old, last);
    }
    newVarsCnt.remove(old);
    if (last != null) {
      for (int i = 1; i < last; ++i) {
        newLocals = VariableDecl.mk(
          null,
          old.getName() + "$$" + i,
          TypeUtils.stripDep(old.getType()).clone(),
          old.getTypeArgs() == null? null :old.getTypeArgs().clone(),
          newLocals);
      }
      newLocals = VariableDecl.mk(
        null,
        old.getName(),
        TypeUtils.stripDep(old.getType()).clone(),
        old.getTypeArgs() == null? null : old.getTypeArgs().clone(),
        newLocals);
    }
    return VariableDecl.mk(
      null,
      old.getName() + (last != null && last > 0? "$$" + last : ""),
      TypeUtils.stripDep(old.getType()).clone(),
      old.getTypeArgs() == null? null : old.getTypeArgs().clone(),
      newResults((VariableDecl)old.getTail()));
  }
}
