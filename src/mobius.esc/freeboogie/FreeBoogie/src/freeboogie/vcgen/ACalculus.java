package freeboogie.vcgen;

import java.util.HashMap;

import genericutils.Logger;
import genericutils.SimpleGraph;

import freeboogie.Main;
import freeboogie.ast.AssertAssumeCmd;
import freeboogie.ast.Block;
import freeboogie.ast.Body;
import freeboogie.ast.Command;
import freeboogie.backend.Term;
import freeboogie.backend.TermBuilder;
import freeboogie.tc.TcInterface;

import static freeboogie.cli.FbCliOptionsInterface.LogCategories;
import static freeboogie.cli.FbCliOptionsInterface.LogLevel;

/**
 * Base class for weakest precondition and strongest postcondition
 * implementations.
 * @param <T> the type of terms
 */
public abstract class ACalculus<T extends Term<T>> {
  protected Logger<LogCategories, LogLevel> log = 
    Logger.<LogCategories, LogLevel>get("log");

  /** the preconditions of each command. */
  protected final HashMap<Block, T> preCache = new HashMap<Block, T>();

  /** the postconditions of each command. */
  protected final HashMap<Block, T> postCache = new HashMap<Block, T>();

  
  /** builds terms for a specific theorem prover. */
  protected TermBuilder<T> term;
  
  protected T trueTerm;
  
  /** the control flow graph currently being processed. */
  protected SimpleGraph<Block> flow;

  protected boolean assumeAsserts;
  
  /** the current body which is being inspected. */
  private Body currentBody;


  private TcInterface tc;
 
  public void setBuilder(TermBuilder<T> term) { 
    this.term = term; 
    trueTerm = term.mk("literal_formula", Boolean.valueOf(true));
  }

  public void typeChecker(TcInterface tc) {
    this.tc = tc;
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
    flow = tc.getFlowGraph(bdy);
    log.say(LogCategories.STATS, LogLevel.INFO, "cfg_size " + flow.nodeCount());
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

  public void assumeAsserts(boolean assumeAsserts) {
    this.assumeAsserts = assumeAsserts;
  }
}
