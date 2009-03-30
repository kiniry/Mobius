package freeboogie.vcgen;

import java.io.PrintWriter;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import freeboogie.ast.AssertAssumeCmd;
import freeboogie.ast.AssignmentCmd;
import freeboogie.ast.Ast;
import freeboogie.ast.AtomId;
import freeboogie.ast.AtomOld;
import freeboogie.ast.BinaryOp;
import freeboogie.ast.Block;
import freeboogie.ast.Body;
import freeboogie.ast.Command;
import freeboogie.ast.Declaration;
import freeboogie.ast.Expr;
import freeboogie.ast.Identifiers;
import freeboogie.ast.Implementation;
import freeboogie.ast.Signature;
import freeboogie.ast.Transformer;
import freeboogie.ast.TupleType;
import freeboogie.ast.Type;
import freeboogie.ast.VariableDecl;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.tc.SPGRecognizer;
import freeboogie.tc.SimpleGraph;
import freeboogie.tc.TcInterface;
import freeboogie.tc.TypeUtils;
import freeboogie.util.Err;

/**
 * Passify option.
 * Implements the algorithm found in the paper 
 * Avoiding Exponential Explosion: Generating Compact Verification Conditions
 * C. Flanagan and J. B. Saxe
 * 
 * 
 * @author J. Charles (julien.charles@gmail.com)
 */
public class Passificator extends Transformer {

  /** the current instance of the type checker. */
  private final TcInterface fTypeChecker;

  /** the main global environment. */
  private final Environment fEnv = new Environment();

  private boolean isVerbose;

  
  /**
   * Construct a passificator, relating to the current instance of the type checker.
   * @param tc the current system type checker
   */
  public Passificator(TcInterface tc, boolean verbose) {
    fTypeChecker = tc;
    isVerbose = verbose;
  }

  /**
   * Process the AST, and returns the modified version.
   * @param ast the ast to look at.
   * @return a valid modified ast
   */
  public Declaration process(final Declaration ast) {
    Declaration passifiedAst = (Declaration)ast.eval(this);
    passifiedAst = addVariableDeclarations(passifiedAst);
    verifyAst(passifiedAst);
    return fTypeChecker.getAST();
  }
  
  @Override
  public Ast eval(VariableDecl decl, String name, 
                  Type type, Identifiers typeVars, Declaration tail) {
    fEnv.addGlobal(decl);
    Declaration newTail = tail != null?(Declaration)tail.eval(this) : null; 
    return VariableDecl.mk(name, type, typeVars, newTail);
  }
  
  
  /**
   * Treats method by methods.
   */
  @Override
  public Implementation eval(Implementation implementation, Signature sig, Body oldBody, Declaration tail) {
    SimpleGraph<Block> currentFG = fTypeChecker.getFlowGraph(implementation);
    SPGRecognizer recog = new SPGRecognizer(currentFG);
    System.err.println("......   " + recog.check());
    Body body = oldBody;
    if (currentFG.hasCycle()) {
      Err.warning("" + implementation.loc() + ": Implementation " + 
        sig.getName() + " has cycles. I'm not passifying it.");
    }
    else {

      BodyPassifier bp = BodyPassifier.passify(fTypeChecker, currentFG, fEnv, 
                                               oldBody, (VariableDecl)sig.getResults());
      sig = Signature.mk(sig.getName(), sig.getArgs(),
                         bp.getResult(),
                         sig.getTypeVars(), sig.loc());
      body = bp.getBody();
      fEnv.updateGlobalWith(bp.getEnvironment());

    }

    // process the rest of the program
    if (tail != null) {
      tail = (Declaration)tail.eval(this);
    }
    return Implementation.mk(sig, body, tail);
  }

  
  
  /**
   * Adds to the AST the variable declarations for the variables
   * that were added by the algorithm.
   * @param ast the AST to transform
   * @return the AST with the added declarations
   */
  private Declaration addVariableDeclarations(Declaration ast) {
    for (Map.Entry<VariableDecl, Integer> e : fEnv.getGlobalSet()) {
      for (int i = 1; i <= e.getValue(); ++i) {
        ast = ABasicPassifier.mkDecl(e.getKey(), i, ast); 
      }
    }
    return ast;
  }

  /**
   * Verify if the AST typechecks well.
   * @param ast
   * @return true if the typechecking works.
   */
  private boolean verifyAst(Declaration ast) {
    if (!fTypeChecker.process(ast).isEmpty()) {
      PrintWriter pw = new PrintWriter(System.out);
      PrettyPrinter pp = new PrettyPrinter(pw);
      ast.eval(pp);
      pw.flush();
      Err.internal(this + " produced invalid Boogie.");
      return false;
    }
    return true;
  }
  
  
  /**
   * 
   * TODO: description
   *
   * @author J. Charles (julien.charles@inria.fr)
   * @author reviewed by TODO
   */
  private static class BodyPassifier extends ABasicPassifier {
    /** the list of local variables declarations. */
    private Declaration newLocals = null;
    /** the current counter associated with each local variable. */
    private final Environment fEnv = new Environment();
    private final Map<Block, Environment> startBlockStatus = 
      new HashMap<Block, Environment> ();
    private final Map<Block, Environment> endBlockStatus = 
      new HashMap<Block, Environment> ();
    private final VariableDecl fResults;
    private final SimpleGraph<Block> fFlowGraph;
    
    private Body fBody;
    private VariableDecl fNewResults;
    /**
     * @param typeChecker  
     * @param flowGraph 
     * @param globalEnv 
     * @param results */
    public BodyPassifier(final TcInterface typeChecker, 
                         final SimpleGraph<Block> flowGraph, 
                         Environment globalEnv, final VariableDecl results) {
      super(typeChecker);
      fResults = results;
      fFlowGraph = flowGraph;
      fEnv.putAll(globalEnv);
    }
    
    public Environment getEnvironment() {
      return fEnv;
    }

    public Body getBody() {
      return fBody;
    }

    public static BodyPassifier passify(TcInterface fTypeChecker, 
                                        SimpleGraph<Block> flowGraph, 
                                        Environment globalEnv, 
                                        Body body, VariableDecl results) {
      BodyPassifier bp = new BodyPassifier(fTypeChecker, flowGraph, globalEnv, results);
      body.eval(bp);
      return bp;
    }

    private void computeDeclarations() {
      fNewResults = newResults(fResults);
      newLocals();
    }
    
    private void newLocals() {
      for (Entry<VariableDecl, Integer> decl: fEnv.getLocalSet()) {
        int last = decl.getValue();
        VariableDecl old = decl.getKey();
        for (int i = 1; i <= last; ++i) {
          newLocals = mkDecl(old, i, newLocals);
        }
      }
    }
    
    private VariableDecl newResults(VariableDecl old) {
      if (old == null) return null;
      int last = fEnv.get(old);
      fEnv.remove(old);
      for (int i = 0; i < last; ++i) {
        newLocals = mkDecl(old, i, newLocals);
      }
      return mkDecl(old, last, newResults((VariableDecl)old.getTail()));
    }
  
    @Override
    public Ast eval(final Body body, Declaration vars, Block blocks) {
      // process out parameters
      newLocals = vars;
      Block newBlocks = (Block) blocks.eval(this);
      computeDeclarations();
      Body newBody = Body.mk(newLocals, newBlocks);
      fBody = newBody;
      return newBody;
    }
    

    
    @Override
    public Block eval(Block block, String name, Command cmd, 
                      Identifiers succ, Block tail) {
            
      Set<Block> blist = fFlowGraph.from(block);
      Environment env = merge(blist);
      if (env == null) {
        env = fEnv.clone();
      }
      startBlockStatus.put(block, env.clone());      
      Command newCmd = cmd == null? null : (Command) cmd.eval(new CommandEvaluator(getTypeChecker(), env));
      endBlockStatus.put(block, env);     
      Block newTail = tail == null? null : (Block) tail.eval(this);
      Identifiers newSucc = succ;
      
      // now we see if we have to add a command to be more proper :P
      Set<Block> succList = fFlowGraph.to(block);
      if (succList.size() == 1) {
        Block next = succList.iterator().next();
        Environment nextEnv = startBlockStatus.get(next);
        for (Entry<VariableDecl, Integer> entry: nextEnv.getAllSet()) {
          VariableDecl decl = entry.getKey();
          int currIdx = env.get(decl);
          int oldIdx = entry.getValue();
          if (oldIdx != currIdx) {
            // we have to add an assume
            AtomId newVar = mkVar(decl, oldIdx);
            AtomId oldVar = mkVar(decl, currIdx);
            Command assumeCmd = mkAssumeEQ(newVar, oldVar);
            String nodeName = name + "$$" + entry.getKey().getName();
            newTail = Block.mk(nodeName, assumeCmd, newSucc, newTail);
            newSucc = Identifiers.mk(AtomId.mk(nodeName, null), null);
          }
        }
      }
      
      fEnv.updateWith(env); 
      return Block.mk(name, newCmd, newSucc, newTail, block.loc());
    }

    /**
     * Merge a list of environments associated with blocks.
     * @param blist
     * @return the merged environment
     */
    private Environment merge(Set<Block> blist) {
      if (blist.size() == 0) {
        return null;
      }
      
      Environment res = new Environment();
      res.putAll(endBlockStatus.get(blist.iterator().next()));
      
      if (blist.size() == 1) {
        return res;
      }
      
      for (Entry<VariableDecl, Integer> entry: res.getAllSet()) {
        VariableDecl decl = entry.getKey();
        int currInc = entry.getValue();
        boolean change = false;
        for (Block b: blist) {
          Integer incarnation = endBlockStatus.get(b).get(decl);
          int inc = incarnation == null ? 0 : incarnation;
          if (currInc!= inc) {
            if (inc > currInc) {
              currInc= incarnation;
            }
            change = true;
          }
        }
        if (change) {
          res.put(decl, currInc + 1);
        }
      }
      
      return res;
    }

    
    /**
     * Returns the new variable representing the result that
     * has been computed by the algorithm.
     * @return the corresponding result variable
     */
    public VariableDecl getResult() {
      return fNewResults;
    }
  }

  private static class CommandEvaluator extends ABasicPassifier {
    Environment env;
    int belowOld = 0;
    
    public CommandEvaluator(TcInterface tc, Environment env) {
      super (tc);
      this.env = env;
    }

    /**
     * Returns a fresh identifier out of an old one.
     * @param var the old id
     * @return an id which was not used before.
     */
    public AtomId fresh(AtomId var) {
      
      VariableDecl decl = getDeclaration(var);
      Integer i = env.get(decl);
      int curr = i == null? 0 : i;
      curr++;
      env.put(decl, curr);
      return mkVar(var, curr);
    }
    
    
    @Override
    public Expr eval(AtomOld atomOld, Expr e) {
      ++belowOld;
      e = (Expr)e.eval(this);
      --belowOld;
      return e;
    }
    
    @Override
    public AssertAssumeCmd eval(final AssignmentCmd assignmentCmd, 
                                final AtomId var, final Expr rhs) {
      AssertAssumeCmd result = null;
      Expr value = (Expr) rhs.eval(this);
      result = mkAssumeEQ(fresh(var), value);
      return result;
    }


    /**
     * Returns a fresh identifier out of an old one.
     * @param var the old id
     * @return an id which was not used before.
     */
    public AtomId get(AtomId var) {
      VariableDecl decl = getDeclaration(var);
      int i = env.get(decl);
      if (belowOld > 0) {
        i = 0;
      }
      return mkVar(var, i);
    }
    
    @Override
    public AtomId eval(AtomId atomId, String id, TupleType types) {
      return get(atomId);
    }
  }
  /**
   * 
   * TODO: description
   *
   * @author J. Charles (julien.charles@inria.fr)
   * @author reviewed by TODO
   */
  public static class Environment {
    /** global variable list. */
    private final Map<VariableDecl, Integer> global = 
      new LinkedHashMap<VariableDecl, Integer>() ;
    /** local variable list. */
    private final Map<VariableDecl, Integer> local = 
      new LinkedHashMap<VariableDecl, Integer>();
    /** for efficiency. */
    private final Map<VariableDecl, Integer> all = 
      new LinkedHashMap<VariableDecl, Integer>();
   
    /** */
    public Environment() {
     // nothing 
    }
    
    /**
     * Adds a variable to the global variables set.
     * @param decl the variable to add
     */
    public void addGlobal(VariableDecl decl) {
      global.put(decl, 0);
      all.put(decl, 0);
    }
    
    /**
     * Put a variable in the environment with its corresponding index.
     * @param decl de variable declaration
     * @param i the index
     */
    public void put(VariableDecl decl, int i) {
      if (global.containsKey(decl)) {
        global.put(decl, i);
      }
      else {
        local.put(decl, i);
      }
      all.put(decl, i);
    }

    /**
     * Returns the global set of variables.
     * @return a set of variables and their indexes
     */
    public Set<Entry<VariableDecl, Integer>> getGlobalSet() {
      return global.entrySet();
    }
    
    /**
     * Returns the local set of variables.
     * @return a set of variables and their indexes
     */
    public Set<Entry<VariableDecl, Integer>> getLocalSet() {
      return local.entrySet();
    }
    
    /**
     * Returns all the collected variables so far.
     * @return a set of variables and their indexes
     */
    public Set<Entry<VariableDecl, Integer>> getAllSet() {
      return all.entrySet();
    }
    
    /**
     * Removes a variable from the environment.
     * @param old the variable to remove
     */
    public void remove(VariableDecl old) {
      global.remove(old);
      local.remove(old);
      all.remove(old);
    }

    public void putAll(Environment env) {
      global.putAll(env.global);
      local.putAll(env.local);
      all.putAll(env.all);
    }

    private Environment(Environment env) {
      putAll(env);
    }

    /**
     * Returns the index corresponding to the given variable
     * @param key the variable to get the index from
     * @return an index > to 0
     */
    public int get(VariableDecl key) {
      Integer i = all.get(key);
      return i == null? 0 : i;
    }
    
    
    @Override
    public Environment clone() {
      return new Environment(this);
    }
    
    /**
     * Update with another environment.
     * ie. if variable index is greater in the other 
     * environment, it replaces the current variable index.
     * @param env the environment to update with.
     */
    public void updateWith(Environment env) {
      update(env.global, global);
      update(env.local, local);
      update(env.all, all);
    }
    
    /**
     * Updates only the global environment with the given values.
     * @param env the environment to update with
     */
    public void updateGlobalWith(Environment env) {
      update(env.global, global);
      all.putAll(global);
    }
    
    private static void update(Map<VariableDecl, Integer> src, 
                               Map<VariableDecl, Integer> target) {

      for (VariableDecl decl: src.keySet()) {
        Integer currInc = target.get(decl);
        int curr = currInc != null? currInc : 0;
        Integer incarnation = src.get(decl);
        if (incarnation > curr) {
              curr = incarnation;
              target.put(decl, curr);
        }
      }
    }
  }
  

  
  public static abstract class ABasicPassifier extends Transformer {

    private final TcInterface fTypeChecker;
    public ABasicPassifier (TcInterface tc) {
      fTypeChecker = tc;
    }
    /**
     * Returns the variable declaration corresponding to the given id.
     * @param id the id to check for
     * @return a valid variable declaration
     */
    VariableDecl getDeclaration(AtomId id) {
      return (VariableDecl) getTypeChecker().getST().ids.def(id);
    }
    public TcInterface getTypeChecker() {
      return fTypeChecker;
    }  
    
    public static AssertAssumeCmd mkAssumeEQ(Expr left, Expr right) {
      return AssertAssumeCmd.mk(AssertAssumeCmd.CmdType.ASSUME, null,
        BinaryOp.mk(BinaryOp.Op.EQ, left, right));
    }
    
    public static AtomId mkVar(VariableDecl decl, int idx) {
      String name = decl.getName();
      if (idx != 0) {
        name += "$$" + idx;
      }
      return AtomId.mk(name, null);
    }
    
    public static AtomId mkVar(AtomId id, int idx) {
      String name = id.getId();
      if (idx != 0) {
        name += "$$" + idx;
      }
      return  AtomId.mk(name, id.getTypes(), id.loc());
    }
    
    public static VariableDecl mkDecl(VariableDecl old, int idx, Declaration next) {
      String name = old.getName();
      if (idx != 0) {
        name += "$$" + idx;
      }
      return VariableDecl.mk(
        name,
        TypeUtils.stripDep(old.getType()).clone(),
        old.getTypeVars() == null? null :old.getTypeVars().clone(),
        next);
    }
   
  }

}
