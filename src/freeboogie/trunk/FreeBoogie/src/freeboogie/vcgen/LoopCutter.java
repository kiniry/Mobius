package freeboogie.vcgen;

import java.io.PrintWriter;
import java.util.HashSet;
import java.util.logging.Logger;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.tc.SimpleGraph;
import freeboogie.tc.TcInterface;
import freeboogie.util.*;

/**
 * Cuts back edges.
 */
public class LoopCutter extends Transformer {
  private static final Logger log = Logger.getLogger("freeboogie.vcgen");

  private TcInterface tc;
  private SimpleGraph<Block> currentFG;

  private HashSet<Block> seen, done;
  private HashSet<Pair<Block, String>> toRemove;
  private String stuckName;
  private boolean hasStuck;

  public LoopCutter() {
    seen = new HashSet<Block>(1009);
    done = new HashSet<Block>(1009);
    toRemove = new HashSet<Pair<Block, String>>(1009);
  }

  public Declaration process(Declaration ast, TcInterface tc) {
    this.tc = tc;
    ast = (Declaration)ast.eval(this);

    if (!tc.process(ast).isEmpty()) {
      PrintWriter pw = new PrintWriter(System.out);
      PrettyPrinter pp = new PrettyPrinter(pw);
      ast.eval(pp); pw.flush();
      Err.fatal("INTERNAL ERROR: LoopCutter produced invalid Boogie.");
    }
    return tc.getAST();
  }

  // === transformer methods ===

  @Override
  public Implementation eval(Implementation implementation, Signature sig, Body body, Declaration tail) {
    Declaration newTail = tail == null? null : (Declaration)tail.eval(this);
    currentFG = tc.getFlowGraph(implementation);
    seen.clear(); done.clear(); toRemove.clear();
    dfs(body.getBlocks());
    hasStuck = false;
    Body newBody = body == null? null : (Body)body.eval(this);
    if (newBody != body || newTail != tail)
      implementation = Implementation.mk(sig, newBody, newTail);
    return implementation;
  }

  @Override
  public Block eval(Block block, String name, Command cmd, Identifiers succ, Block tail) {
    Pair<Block, String> pair = new Pair<Block, String>(block, null);
    boolean same = true;
    Identifiers newSucc = null;
    if (succ != null) {
      while (succ != null) {
        pair.second = succ.getId().getId();
        if (toRemove.contains(pair))
          same = false;
        else
          newSucc = Identifiers.mk(succ.getId(), newSucc);
        succ = succ.getTail();
      }
      if (newSucc == null) {
        if (!hasStuck) {
          hasStuck = true;
          stuckName = Id.get("stuck");
        }
        newSucc = Identifiers.mk(AtomId.mk(stuckName, null), null);
      }
    }
    Block newTail;
    if (tail == null) {
      newTail = !hasStuck? null : Block.mk(
        stuckName,
        AssertAssumeCmd.mk(
          AssertAssumeCmd.CmdType.ASSUME,
          null,
          AtomLit.mk(AtomLit.AtomType.FALSE)),
        null,
        null);
    } else
      newTail = (Block)tail.eval(this);
    return Block.mk(name, cmd, newSucc, newTail);
  }

  // === depth first search for back edges ===

  private void dfs(Block b) {
    if (b == null) return;
    seen.add(b);
    for (Block c : currentFG.to(b)) {
      if (done.contains(c)) continue;
      if (seen.contains(c))
        toRemove.add(new Pair<Block, String>(b, c.getName()));
      else
        dfs(c);
    }
    done.add(b);
  }
}
