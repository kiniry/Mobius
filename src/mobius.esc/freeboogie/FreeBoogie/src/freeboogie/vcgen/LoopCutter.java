package freeboogie.vcgen;

import java.util.HashSet;
import java.util.logging.Logger;

import genericutils.*;

import freeboogie.ast.*;
import freeboogie.tc.TcInterface;
import freeboogie.tc.TypeUtils;

/**
 * Cuts back edges and removes unreachable blocks. (Back edges
 * according to some arbitrary DFS.
 */
public class LoopCutter extends Transformer {
  private static final Logger log = Logger.getLogger("freeboogie.vcgen");

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

  // === transformer methods ===

  @Override
  public Implementation eval(
    Implementation implementation,
    Attribute attr,
    Signature sig,
    Body body,
    Declaration tail
  ) {
    Declaration newTail = tail == null? null : (Declaration)tail.eval(this);
    currentFG = tc.getFlowGraph(implementation);
    seen.clear(); done.clear(); toRemove.clear();
    dfs(body.getBlocks());
    hasStuck = false;
    Body newBody = (Body)body.eval(this);
    if (newBody != body || newTail != tail)
      implementation = Implementation.mk(attr, sig, newBody, newTail);
    return implementation;
  }

  @Override
  public Block eval(Block block, String name, Command cmd, Identifiers succ, Block tail) {
    Pair<Block, String> pair = Pair.of(block, null);
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
    if (seen.contains(block))
      return Block.mk(name, cmd, newSucc, newTail);
    else
      return newTail;
  }

  // === depth first search for back edges ===

  private void dfs(Block b) {
    if (b == null) return;
    seen.add(b);
    for (Block c : currentFG.to(b)) {
      if (done.contains(c)) continue;
      if (seen.contains(c))
        toRemove.add(Pair.of(b, c.getName()));
      else
        dfs(c);
    }
    done.add(b);
  }
}
