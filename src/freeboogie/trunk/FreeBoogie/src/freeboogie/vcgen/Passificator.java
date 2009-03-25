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
import freeboogie.ast.VariableDecl;
import freeboogie.astutil.PrettyPrinter;
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
 * TODO: fix the global env stuff
 * 
 * @author J. Charles (julien.charles@gmail.com)
 */
public class Passificator extends Transformer {

  /** the current instance of the type checker. */
  private final TcInterface fTypeChecker;

  private final Environment fGlobalVarsCnt = new Environment();

  
  /**
   * Construct a passificator, relating to the current instance of the type checker.
   * @param tc the current system type checker
   */
  public Passificator(TcInterface tc) {
    fTypeChecker = tc;
  }

  
  public Declaration process(final Declaration ast) {
    Declaration passifiedAst = (Declaration)ast.eval(this);
    passifiedAst = addVariableDeclarations(passifiedAst);
    verifyAst(passifiedAst);
    return fTypeChecker.getAST();
  }
  
  /**
   * Treats method by methods.
   */
  @Override
  public Implementation eval(Implementation implementation, Signature sig, Body oldBody, Declaration tail) {
    SimpleGraph<Block> currentFG = fTypeChecker.getFlowGraph(implementation);
    Body body = oldBody;
    if (currentFG.hasCycle()) {
      Err.warning("" + implementation.loc() + ": Implementation " + 
        sig.getName() + " has cycles. I'm not passifying it.");
    }
    else {

      BodyPassifier bp = BodyPassifier.passify(fTypeChecker, currentFG, oldBody, (VariableDecl)sig.getResults());
      sig = Signature.mk(sig.getName(), sig.getArgs(),
                         bp.getResult(),
                         sig.getTypeVars(), sig.loc());
      body = bp.getBody();

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
    for (Map.Entry<VariableDecl, Integer> e : fGlobalVarsCnt.entrySet()) {
      for (int i = 1; i <= e.getValue(); ++i) {
        Identifiers ntv = e.getKey().getTypeVars();
        if (ntv != null) ntv = ntv.clone();
        ast = VariableDecl.mk(
          e.getKey().getName()+"$$"+i, 
          TypeUtils.stripDep(e.getKey().getType()).clone(), 
          ntv, 
          ast);
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
  
  private static class BodyPassifier extends Transformer {
    /** the list of local variables declarations. */
    private Declaration newLocals = null;
    /** the current counter associated with each local variable. */
    private final Environment fLocalVarsCnt = new Environment();
    private final Map<Block, Environment> startBlockStatus = 
      new HashMap<Block, Environment> ();
    private final Map<Block, Environment> endBlockStatus = 
      new HashMap<Block, Environment> ();
    private final VariableDecl fResults;
    private final TcInterface fTypeChecker;
    private final SimpleGraph<Block> fFlowGraph;
    
    private Body fBody;
    private VariableDecl fNewResults;
    /**
     * @param typeChecker  
     * @param flowGraph 
     * @param results */
    public BodyPassifier(final TcInterface typeChecker, 
                         final SimpleGraph<Block> flowGraph, 
                         final VariableDecl results) {
      fTypeChecker = typeChecker;
      fResults = results;
      fFlowGraph = flowGraph;
    }
    
    public Body getBody() {
      return fBody;
    }

    public static BodyPassifier passify(TcInterface fTypeChecker, 
                                        SimpleGraph<Block> flowGraph, 
                                        Body body, VariableDecl results) {
      BodyPassifier bp = new BodyPassifier(fTypeChecker, flowGraph, results);
      body.eval(bp);
      return bp;
    }

    private void computeDeclarations() {
      fNewResults = newResults(fResults);
      newLocals();
    }
    
    private void newLocals() {
      for (Entry<VariableDecl, Integer> decl: fLocalVarsCnt.entrySet()) {
        int last = decl.getValue();
        VariableDecl old = decl.getKey();
        for (int i = 1; i <= last; ++i) {
          newLocals = mkDecl(old, i, newLocals);
        }
      }
    }
    
    private VariableDecl newResults(VariableDecl old) {
      if (old == null) return null;
      int last = fLocalVarsCnt.get(old);
      fLocalVarsCnt.remove(old);
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
        env = fLocalVarsCnt.clone();
      }
      startBlockStatus.put(block, env.clone());      
      Command newCmd = cmd == null? null : (Command) cmd.eval(new CommandEvaluator(env));
      endBlockStatus.put(block, env);     
      Block newTail = tail == null? null : (Block) tail.eval(this);
      Identifiers newSucc = succ;
      
      // now we see if we have to add a command to be more proper :P
      Set<Block> succList = fFlowGraph.to(block);
      if (succList.size() == 1) {
        Block next = succList.iterator().next();
        Environment nextEnv = startBlockStatus.get(next);
        for (Entry<VariableDecl, Integer> entry: nextEnv.entrySet()) {
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
      
      updateWith(env); 
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
      
      for (VariableDecl decl: res.keySet()) {
        int currInc= res.get(decl);
        for (Block b: blist) {
          Integer incarnation = endBlockStatus.get(b).get(decl);
          int inc = incarnation == null ? 0 : incarnation;
          if (currInc!= inc) {
            if (inc > currInc) {
              currInc= incarnation;
            }
          }
        }
        res.put(decl, currInc + 1);
      }
      
      return res;
    }
    
    private void updateWith(Environment env) {

      for (VariableDecl decl: env.keySet()) {
        Integer currInc = fLocalVarsCnt.get(decl);
        int curr = currInc != null? currInc : 0;
        Integer incarnation = env.get(decl);
        if (incarnation > curr) {
              curr = incarnation;
              fLocalVarsCnt.put(decl, curr);
        }
      }
    }
    
    /**
     * Returns the new variable representing the result that
     * has been computed by the algorithm.
     * @return the corresponding result variable
     */
    public VariableDecl getResult() {
      return fNewResults;
    }



    /**
     * Returns the variable declaration corresponding to the given id.
     * @param id the id to check for
     * @return a valid variable declaration
     */
    VariableDecl getDeclaration(AtomId id) {
      return (VariableDecl) fTypeChecker.getST().ids.def(id);
    }
    
    private class CommandEvaluator extends Transformer {
      Environment env;
      int belowOld = 0;
      
      public CommandEvaluator(Environment env) {
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
  }

  private static class Environment extends  LinkedHashMap<VariableDecl, Integer> { 
    public Environment() {
     // nothing 
    }
    public int get(VariableDecl key) {
      Integer i = super.get(key);
      return i == null? 0 : i;
    }
    
    @Override
    public Environment clone() {
      return (Environment) super.clone();
    }
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
