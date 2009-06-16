package freeboogie.vcgen;

import java.util.HashMap;
import java.util.logging.Logger;

import genericutils.SimpleGraph;

import freeboogie.Main;
import freeboogie.ast.AssertAssumeCmd;
import freeboogie.ast.Block;
import freeboogie.ast.Body;
import freeboogie.ast.Command;
import freeboogie.backend.Term;
import freeboogie.backend.TermBuilder;
import freeboogie.tc.TcInterface;

/**
 * Base class for weakest precondition and strongest postcondition
 * implementations.
 * @param <T> the type of terms
 */
public abstract class ACalculus<T extends Term<T>> {
  /** Used mainly for debugging. */
  protected static final Logger log = Logger.getLogger("freeboogie.vcgen");

  /** the preconditions of each command. */
  protected final HashMap<Block, T> preCache = new HashMap<Block, T>();

  /** the postconditions of each command. */
  protected final HashMap<Block, T> postCache = new HashMap<Block, T>();

  
  /** builds terms for a specific theorem prover. */
  protected TermBuilder<T> term;
  
  protected T trueTerm;
  
  /** the control flow graph currently being processed. */
  protected SimpleGraph<Block> flow;
  
  /** the current body which is being inspected. */
  private Body currentBody;


  private final TcInterface tc;
  
  public ACalculus(TcInterface tc) {
    this.tc = tc;
  }
  
  
  public void setBuilder(TermBuilder<T> term) { 
    this.term = term; 
    trueTerm = term.mk("literal_formula", Boolean.valueOf(true));
  }
  
  public void resetCache() {
    preCache.clear();
    postCache.clear();
  }
  
  /**
   * Sets the flow graph to be processed by the next calls to
   * {@code pre}, {@code post}, and {@code vc}. This class
   * assumes that {@code flow} won't be changed.
   */
  public void setCurrentBody(Body bdy) {
    log.info("prepare to compute sp on a new flow graph");
    flow = tc.getFlowGraph(bdy);
    if (false) { // TODO: log-categ
      System.out.println("Flow graph size " + flow.nodesInTopologicalOrder().size());
    }
    currentBody = bdy;
    assert flow.isFrozen();
    assert !flow.hasCycle(); // please cut loops first
    resetCache();
  }

  /**
   * Returns a verification condition for the whole flow graph.
   * @return a term representing the vc
   */
  public abstract T vc();
  
  // === helpers ===
  public static boolean is(Block b, AssertAssumeCmd.CmdType t) {
    if (b == null) return false;
    Command c = b.getCmd();
    if (!(c instanceof AssertAssumeCmd)) return false;
    return ((AssertAssumeCmd)c).getType() == t;
  }

  public static boolean isAssume(Block b) {
    return is(b, AssertAssumeCmd.CmdType.ASSUME);
  }

  public static boolean isAssert(Block b) {
    return is(b, AssertAssumeCmd.CmdType.ASSERT);
  }

  public T term(Block b) {
    if (b == null) return trueTerm;
    Command c = b.getCmd();
    if (!(c instanceof AssertAssumeCmd)) return trueTerm;
    return term.of(((AssertAssumeCmd)c).getExpr());
  }


  public Body getCurrentBody() {
    return currentBody;
  }

  public TcInterface getTypeChecker() {
    return tc;
  }
}
