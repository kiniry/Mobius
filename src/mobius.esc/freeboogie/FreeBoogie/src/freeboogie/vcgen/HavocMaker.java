package freeboogie.vcgen;

import java.util.*;

import genericutils.*;

import freeboogie.ast.*;
import freeboogie.tc.TcInterface;
import freeboogie.tc.TypeUtils;

/**
 * Havocs variables potentially assigned to in loops at the entry point
 * of the loop.
 */
public class HavocMaker extends Transformer {
  /* IMPLEMENTATION
   * 1. construct maps
   *      A: block -> scc
   *      B: entry point -> scc    (a submap of the above)
   *      C: scc -> set of vars potentially assigned to
   * 2. replace each entry point e by
   *      havoc C(B(e)); goto old_e
   *
   * The first step can be done with the Kosaraju algo for scc.
   * If we do the ordering with normal edges and the tagging
   * with reversed edges then, while we do the tagging we also
   * see the entry points as nodes from which you can reach
   * (backwards) nodes that are already in another scc.
   */
  private HashSet<Block> seen = new HashSet<Block>();
  private HashMap<Block, Integer> scc = new HashMap<Block, Integer>();
  private HashMap<Block, Integer> sccOfEntryPoint = new HashMap<Block, Integer>();
  private ArrayList<HashSet<String>> assignedVars = new ArrayList<HashSet<String>>();
  private ArrayList<Integer> sccSize = new ArrayList<Integer>();

  private int sccIndex; // the index of the scc being built
  private HashSet<String> sccAssignedVars; 
    // variables assigned in the scc being processed
  private ArrayList<Block> dfs2order = new ArrayList<Block>();

  private SimpleGraph<Block> flowGraph;

  private ReadWriteSetFinder rw;

  @Override
  public Declaration process(Declaration ast, TcInterface tc) {
    this.tc = tc;
    rw = new ReadWriteSetFinder(tc.getST());
    ast = (Declaration)ast.eval(this);
    ast = TypeUtils.internalTypecheck(ast, tc);
    return ast;
  }

  @Override
  public Implementation eval(
    Implementation implementation,
    Attribute attr,
    Signature sig,
    Body body,
    Declaration tail
  ) {
    Declaration newTail = tail == null? null : (Declaration)tail.eval(this);

    flowGraph = tc.getFlowGraph(implementation);
    seen.clear(); seen.add(null); dfs2order.clear();
    dfs1(body.getBlocks());
    Collections.reverse(dfs2order);

    scc.clear(); sccOfEntryPoint.clear(); 
    assignedVars.clear(); sccSize.clear();
    sccIndex = -1;
    for (Block b : dfs2order) if (scc.get(b) == null) {
      sccSize.add(0);
      ++sccIndex;
      sccAssignedVars = new HashSet<String>();
      assignedVars.add(sccAssignedVars);
      dfs2(b);
    }

    Body newBody = (Body)body.eval(this);
    if (newTail != tail || newBody != body)
      implementation = Implementation.mk(attr, sig, newBody, newTail);
    return implementation;
  }

  @Override
  public Block eval(Block block, String name, Command cmd, Identifiers succ, Block tail) {
    Block newTail = tail == null? null : (Block)tail.eval(this);
    Integer blockScc = sccOfEntryPoint.get(block);
//System.out.println("process " + name);
    if (blockScc != null 
        && sccSize.get(blockScc) > 1 
        && !assignedVars.get(blockScc).isEmpty()) {
//System.out.println("change " + name);
      String tmpName = Id.get("loop_entry");
      block = Block.mk(tmpName, cmd, succ, newTail);
      block = Block.mk(
        name,
        HavocCmd.mk(idsFromStrings(assignedVars.get(blockScc))),
        Identifiers.mk(AtomId.mk(tmpName, null), null),
        block);
    } else if (newTail != tail) {
//System.out.println("don't change " + name);
      block = Block.mk(name, cmd, succ, newTail);
    }
    return block;
  }

  // === scc ===

  private void dfs1(Block b) {
    if (seen.contains(b)) return;
    seen.add(b);
//System.out.println("dfs1 " + b.getName());
    for (Block c : flowGraph.to(b)) dfs1(c);
    dfs2order.add(b);
  }

  private void dfs2(Block b) {
    scc.put(b, sccIndex);
    sccSize.set(sccIndex, 1 + sccSize.get(sccIndex));
//System.out.println("dfs2 " + b.getName() + ", idx " + sccIndex);

    Command cmd = b.getCmd();
    if (cmd != null) {
      Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> rwVars = cmd.eval(rw);
      for (VariableDecl vd : rwVars.second)
        sccAssignedVars.add(vd.getName());
    }

    for (Block c : flowGraph.from(b)) {
      Integer cScc = scc.get(c);
      if (cScc == null)
        dfs2(c);
      else if (cScc != sccIndex)
        sccOfEntryPoint.put(b, sccIndex);
    }
  }

  // === helpers ===

  private Identifiers idsFromStrings(Iterable<String> sl) {
    Identifiers r = null;
    for (String s : sl) r = Identifiers.mk(AtomId.mk(s, null), r);
    return r;
  }
}
