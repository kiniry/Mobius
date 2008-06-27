package freeboogie.vcgen;

import java.util.*;
import java.util.logging.Logger;

import freeboogie.ast.*;
import freeboogie.tc.*;
import freeboogie.util.*;

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
  static private final Logger log = Logger.getLogger("freeboogie.vcgen");

  private TcInterface tc;
  private HashMap<VariableDecl, HashMap<Command, Integer>> readIdx;
  private HashMap<VariableDecl, HashMap<Command, Integer>> writeIdx;
  private HashMap<VariableDecl, Integer> newVarsCnt;
  private HashMap<Command, HashSet<VariableDecl>> commandWs;
  private ReadWriteSetFinder rwsf;

  private VariableDecl currentVar;
  private HashMap<Command, Integer> currentReadIdxCache;
  private HashMap<Command, Integer> currentWriteIdxCache;
  private SimpleGraph<Block> currentFG;
  private Command currentCommand;

  private Deque<Boolean> context; // true = write, false = read
  private int belowOld;

  // === public interface ===
  
  public Declaration process(Declaration ast, TcInterface tc) {
    this.tc = tc;
    readIdx = new LinkedHashMap<VariableDecl, HashMap<Command, Integer>>();
    writeIdx = new LinkedHashMap<VariableDecl, HashMap<Command, Integer>>();
    newVarsCnt = new LinkedHashMap<VariableDecl, Integer>();
    commandWs = new LinkedHashMap<Command, HashSet<VariableDecl>>();
    rwsf = new ReadWriteSetFinder(tc.getST());
    ast = (Declaration)ast.eval(this);
    for (Map.Entry<VariableDecl, Integer> e : newVarsCnt.entrySet())
      System.out.println(">" + e.getKey().getName() + ":" + e.getValue());
    // TODO Add new globals
    return ast;
  }

  // === (block) transformers ===

  @Override
  public Implementation eval(Implementation implementation, Signature sig, Body body, Declaration tail) {
    currentFG = tc.getFlowGraph(implementation);
    assert currentFG != null; // You should tell me the flowgraph beforehand
    assert !currentFG.hasCycle(); // You should cut cycles first

    // Collect all variables that are assigned to
    Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> rwIds = 
      implementation.eval(rwsf);
    HashSet<VariableDecl> allIds = new HashSet<VariableDecl>();
    for (VariableDecl vd : rwIds.second) allIds.add(vd);

    for (VariableDecl vd : allIds) {
      currentVar = vd;
      currentReadIdxCache = new LinkedHashMap<Command, Integer>();
      currentWriteIdxCache = new LinkedHashMap<Command, Integer>();
      readIdx.put(vd, currentReadIdxCache);
      writeIdx.put(vd, currentWriteIdxCache);
      currentFG.iterNode(new Closure<Block>() {
        @Override public void go(Block b) {
          compReadIdx(b); compWriteIdx(b);
        }
      });
    }

    context = new ArrayDeque<Boolean>();
    context.addFirst(false);
    currentCommand = null;
    belowOld = 0;
    body = (Body)body.eval(this);
    context = null;
    currentFG = null;

    if (tail != null) tail = (Declaration)tail.eval(this);
    return Implementation.mk(sig, body, tail);
  }


  // === workers ===

  private int compReadIdx(Block b) {
    if (currentReadIdxCache.containsKey(b.getCmd()))
      return currentReadIdxCache.get(b.getCmd());
    int ri = 0;
    for (Block pre : currentFG.from(b))
      ri = Math.max(ri, compWriteIdx(pre));
    currentReadIdxCache.put(b.getCmd(), ri);
    return ri;
  }

  private int compWriteIdx(Block b) {
    if (currentWriteIdxCache.containsKey(b.getCmd()))
      return currentWriteIdxCache.get(b.getCmd());
    int wi = compReadIdx(b);
    HashSet<VariableDecl> ws = commandWs.get(b.getCmd());
    if (ws == null) {
      ws = new LinkedHashSet<VariableDecl>();
      for (VariableDecl vd : rwsf.get(b.getCmd()).second) ws.add(vd);
      commandWs.put(b.getCmd(), ws);
    }
    if (ws.contains(currentVar)) ++wi;
    currentWriteIdxCache.put(b.getCmd(), wi);
    int owi = newVarsCnt.containsKey(currentVar) ? newVarsCnt.get(currentVar) : 0;
    newVarsCnt.put(currentVar, Math.max(owi, wi));
    return wi;
  }


  // === visitors ===
  public AssertAssumeCmd eval(AssertAssumeCmd assertAssumeCmd, AssertAssumeCmd.CmdType type, Identifiers typeVars, Expr expr) {
    currentCommand = assertAssumeCmd;
    Expr newExpr = (Expr)expr.eval(this);
    currentCommand = null;
    if (newExpr != expr)
      return AssertAssumeCmd.mk(type, typeVars, newExpr);
    return assertAssumeCmd;
  }

  @Override
  public AssertAssumeCmd eval(AssignmentCmd assignmentCmd, Expr lhs, Expr rhs) {
    AssertAssumeCmd result = null;
    currentCommand = assignmentCmd;
    Expr value = (Expr)rhs.eval(this);
    if (lhs instanceof AtomId) {
      AtomId id = (AtomId)lhs;
      VariableDecl vd = (VariableDecl)tc.getST().ids.def(id);
      result = AssertAssumeCmd.mk(AssertAssumeCmd.CmdType.ASSUME, null,
        BinaryOp.mk(BinaryOp.Op.EQ,
          AtomId.mk(id.getId()+"$$"+getIdx(writeIdx, vd), id.getTypes(), id.loc()),
          value));
    } else if (lhs instanceof AtomIdx) {
      AtomIdx ai = (AtomIdx)lhs;
      AtomId id = (AtomId)ai.getAtom();
      Index idx = ai.getIdx();
      VariableDecl vd = (VariableDecl)tc.getST().ids.def(id);
      Exprs indexAndValue = Exprs.mk(value, null);
      String name = "$$UPDATE1D";
      if (idx.getB() != null) {
        name = "$$UPDATE2D";
        indexAndValue = Exprs.mk((Expr)idx.getB().eval(this), indexAndValue);
      }
      indexAndValue = Exprs.mk((Expr)idx.getA().eval(this), indexAndValue);
      result = AssertAssumeCmd.mk(AssertAssumeCmd.CmdType.ASSUME, null,
        BinaryOp.mk(
          BinaryOp.Op.EQ,
          AtomId.mk(id.getId()+"$$"+getIdx(writeIdx, vd), id.getTypes(), id.loc()),
          AtomFun.mk(
            name,
            null,
            Exprs.mk(AtomId.mk(id.getId()+"$$"+getIdx(readIdx,vd), id.getTypes()),
            indexAndValue))));
    } else assert false; // Hmm, what could it be?
    currentCommand = null;
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
    if (currentCommand == null) return atomId;
    Declaration d = tc.getST().ids.def(atomId);
    if (!(d instanceof VariableDecl)) return atomId;
    VariableDecl vd = (VariableDecl)d;
    int idx = context.getFirst() ? getIdx(writeIdx, vd) : getIdx(readIdx, vd);
    if (idx == 0) return atomId;
    return AtomId.mk(id + "$$" + idx, types, atomId.loc());
  }

  // === helpers ===
  private int getIdx(HashMap<VariableDecl, HashMap<Command, Integer> > cache, VariableDecl vd) {
    if (belowOld > 0) return 0;
    Map<Command, Integer> m = cache.get(vd);
    if (m == null) return 0; // this variable is never written to
    return m.get(currentCommand);
  }
}
