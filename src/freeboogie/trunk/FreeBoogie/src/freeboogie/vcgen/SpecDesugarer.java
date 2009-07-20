package freeboogie.vcgen;

import java.io.PrintWriter;
import java.util.*;
import java.util.logging.Logger;

import genericutils.*;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.tc.*;

/**
 * For each implementation inserts assumes and assert corresponding
 * to the preconditions and postconditions of the procedure.
 *
 * Given:
 * <pre>
 * procedure X(x : int) returns (y : int);
 *   requires x &gt; 0;
 *   ensures y % 2 == 0;
 * </pre>
 *
 * The code
 * <pre>
 * implementation X(v : int) returns (w : int) {
 *    var z : int;
 * a: z := v / 2; goto b;
 * b: w := z * 2;
 * }
 * </pre>
 * becomes
 * <pre>
 * implementation X(v : int) returns (w : int) {
 *       var z : int;
 * pre:  assume v &gt; 0; goto a;
 * a:    z := v / 2;      goto b;
 * b:    w := z * 2;      goto post;
 * post: assert w % 2 == 0;
 * }
 * </pre>
 *
 * NOTE: Free ensures are ignored.
 *
 * TODO: Take care of generics.
 */
public class SpecDesugarer extends Transformer {
  private static final Logger log = Logger.getLogger("freeboogie.vcgen");

  private UsageToDefMap<Implementation, Procedure> implProc;
  private UsageToDefMap<VariableDecl, VariableDecl> paramMap;
  private Map<VariableDecl, AtomId> toSubstitute;
  private List<Expr> preconditions;
  private List<Expr> postconditions;
  private String afterBody;
  private boolean exitPointFound;

  public SpecDesugarer() {
    toSubstitute = new LinkedHashMap<VariableDecl, AtomId>(23);
    preconditions = new ArrayList<Expr>(23);
    postconditions = new ArrayList<Expr>(23);
  }

  /** Transforms the {@code ast} and updates the typechecker. */
  @Override
  public Declaration process(Declaration ast, TcInterface tc) {
    this.tc = tc; 
    implProc = tc.getImplProc();
    paramMap = tc.getParamMap();
    return TypeUtils.internalTypecheck(ast, tc);
  }

  @Override
  public Implementation eval(
    Implementation implementation,
    Attribute attr,
    Signature sig,
    Body body, 
    Declaration tail
  ) {
    // prepare substitutions to be applied to preconditions and postconditions
    toSubstitute.clear();
    VariableDecl pd; // parameter declaration
    for (pd = (VariableDecl)sig.getArgs(); pd != null; pd = (VariableDecl)pd.getTail())
      toSubstitute.put(paramMap.def(pd), AtomId.mk(pd.getName(), null));
    for (pd = (VariableDecl)sig.getResults(); pd != null; pd = (VariableDecl)pd.getTail())
      toSubstitute.put(paramMap.def(pd), AtomId.mk(pd.getName(), null));

    // collect preconditions and postconditions
    Specification spec = implProc.def(implementation).getSpec();
    preconditions.clear();
    postconditions.clear();
    while (spec != null) {
      switch (spec.getType()) {
      case REQUIRES:
        preconditions.add(((Expr)spec.getExpr().eval(this)).clone());
        break;
      case ENSURES:
        if (!spec.getFree()) 
          postconditions.add(((Expr)spec.getExpr().eval(this)).clone());
        break;
      default: // do nothing
      }
      spec = spec.getTail();
    }
    toSubstitute.clear();

    // the rest
    Body newBody = (Body)body.eval(this);
    Declaration newTail = tail == null? null : (Declaration)tail.eval(this);
    if (newBody != body || newTail != tail)
      implementation = Implementation.mk(attr, sig, newBody, newTail, implementation.loc());
    return implementation;
  }

  @Override
  public AtomId eval(AtomId atomId, String id, TupleType types) {
    Declaration d = tc.getST().ids.def(atomId);
    AtomId s = toSubstitute.get(d);
    return s == null? atomId : s;
  }

  @Override
  public Body eval(Body body, Declaration vars, Block blocks) {
    String nxtLabel, crtLabel;
    afterBody = postconditions.isEmpty()? null : Id.get("post");
    String afterPre = blocks != null? blocks.getName() : afterBody;
    Block newBlocks = blocks;
    exitPointFound = false;
    if (newBlocks != null && !postconditions.isEmpty())
      newBlocks = (Block)newBlocks.eval(this);
    if (!exitPointFound) postconditions.clear();
    nxtLabel = null;
    for (Expr post : postconditions) {
      newBlocks = Block.mk(
        crtLabel = Id.get("post"),
        AssertAssumeCmd.mk(AssertAssumeCmd.CmdType.ASSERT, null, post),
        succ(nxtLabel),
        newBlocks);
      nxtLabel = crtLabel;
    }
    if (afterBody != null && exitPointFound)
      newBlocks = Block.mk(afterBody, null, succ(nxtLabel), newBlocks);
    nxtLabel = afterPre;
    for (Expr pre : preconditions) {
      newBlocks = Block.mk(
        crtLabel = Id.get("pre"),
        AssertAssumeCmd.mk(AssertAssumeCmd.CmdType.ASSUME, null, pre),
        succ(nxtLabel),
        newBlocks);
      nxtLabel = crtLabel;
    }
    if (preconditions.isEmpty() && !postconditions.isEmpty())
      newBlocks = Block.mk(Id.get("entry"), null, succ(afterPre), newBlocks);
    if (newBlocks != blocks)
      body = Body.mk(vars, newBlocks, body.loc());
    return body;
  }

  @Override
  public Block eval(Block block, String name, Command cmd, Identifiers succ, Block tail) {
    exitPointFound |= succ == null;
    Block newTail = tail == null? null : (Block)tail.eval(this);
    Identifiers newSucc = succ == null? succ(afterBody) : succ;
    if (newSucc != succ || newTail != tail)
      block = Block.mk(name, cmd, newSucc, newTail, block.loc());
    return block;
  }

  // === helpers ===
  private static Identifiers succ(String blockName) {
    if (blockName == null) return null;
    return Identifiers.mk(AtomId.mk(blockName, null), null);
  }

}
