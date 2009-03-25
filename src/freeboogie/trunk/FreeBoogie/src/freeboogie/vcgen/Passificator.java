package freeboogie.vcgen;

import java.io.PrintWriter;
import java.util.*;
import java.util.Map.Entry;
import java.util.logging.Logger;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.tc.*;
import freeboogie.util.*;

/**
 * Passify option.
 * Implements the algorithm found in the paper 
 * Avoiding Exponential Explosion: Generating Compact Verification Conditions
 * C. Flanagan and J. B. Saxe
 * 
 * @author J. Charles (julien.charles@gmail.com)
 */
public class Passificator extends Transformer {
  // used mainly for debugging
  static private final Logger log = Logger.getLogger("freeboogie.vcgen");
  
  /** the current instance of the type checker. */
  private final TcInterface fTypeChecker;

  private final HashMap<VariableDecl, Integer> fGlobalVarsCnt = 
    new LinkedHashMap<VariableDecl, Integer>();

  
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
          newLocals = VariableDecl.mk(
            old.getName() + "$$" + i,
            TypeUtils.stripDep(old.getType()).clone(),
            old.getTypeVars() == null? null :old.getTypeVars().clone(),
            newLocals);
        }
      }
    }
    
    private VariableDecl newResults(VariableDecl old) {
      if (old == null) return null;
      Integer last = fLocalVarsCnt.get(old);
      fLocalVarsCnt.remove(old);
      if (last != null) {
        for (int i = 1; i < last; ++i) {
          newLocals = VariableDecl.mk(
            old.getName() + "$$" + i,
            TypeUtils.stripDep(old.getType()).clone(),
            old.getTypeVars() == null? null :old.getTypeVars().clone(),
            newLocals);
        }
        newLocals = VariableDecl.mk(
          old.getName(),
          TypeUtils.stripDep(old.getType()).clone(),
          old.getTypeVars() == null? null : old.getTypeVars().clone(),
          newLocals);
      }
      
      return VariableDecl.mk(
        old.getName() + (last != null && last > 0? "$$" + last : ""),
        TypeUtils.stripDep(old.getType()).clone(),
        old.getTypeVars() == null? null : old.getTypeVars().clone(),
        newResults((VariableDecl)old.getTail()));
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
        env = (Environment) fLocalVarsCnt.clone();
      }
      startBlockStatus.put(block, (Environment) env.clone());      
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
          int curr = env.get(entry.getKey());
          if (entry.getValue() != curr) {
            // we have to add an assume
            AtomId newVar = AtomId.mk(entry.getKey().getName() + "$$" + entry.getValue(),
                                      null);
            AtomId oldVar = AtomId.mk(entry.getKey().getName() + "$$" + curr, null);
            Command assumeCmd = AssertAssumeCmd.mk(AssertAssumeCmd.CmdType.ASSUME, 
                                                   null,
                                                   BinaryOp.mk(BinaryOp.Op.EQ,
                                                     newVar, oldVar));
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
        int currIncarnation = res.get(decl);
        for (Block b: blist) {
          Integer incarnation = endBlockStatus.get(b).get(decl);
          if (currIncarnation != incarnation) {
            if (incarnation > currIncarnation) {
              currIncarnation = incarnation;
            }
          }
        }
        res.put(decl, currIncarnation + 1);
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
    private VariableDecl getDeclaration(AtomId id) {
      return (VariableDecl) fTypeChecker.getST().ids.def(id);
    }
    
    private class CommandEvaluator extends Transformer {
      Environment env;
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
        return AtomId.mk(var.getId()+"$$" + curr, 
                         var.getTypes(), 
                         var.loc()); 
      }
      
      @Override
      public AssertAssumeCmd eval(final AssignmentCmd assignmentCmd, 
                                  final AtomId var, final Expr rhs) {
        AssertAssumeCmd result = null;
        Expr value = (Expr) rhs.eval(this);
        result = AssertAssumeCmd.mk(AssertAssumeCmd.CmdType.ASSUME, null,
            BinaryOp.mk(BinaryOp.Op.EQ,
                        fresh(var), value));
        return result;
      }


      /**
       * Returns a fresh identifier out of an old one.
       * @param var the old id
       * @return an id which was not used before.
       */
      public AtomId get(AtomId var) {
        
        VariableDecl decl = getDeclaration(var);
        Integer i = env.get(decl);
        String name;
        if (i == null) {//FIXME: should do the old here too
          name = var.getId();
        }
        else {
          name = var.getId()+"$$" + i;
        }
        
        return AtomId.mk(name,
                         var.getTypes(), 
                         var.loc()); 
      }
      
      @Override
      public AtomId eval(AtomId atomId, String id, TupleType types) {
        return get(atomId);
      }
    }
  }

  private static class Environment extends  LinkedHashMap<VariableDecl, Integer> { }
}
