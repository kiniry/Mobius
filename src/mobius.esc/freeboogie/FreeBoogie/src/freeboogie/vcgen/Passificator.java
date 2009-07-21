package freeboogie.vcgen;

import java.io.PrintWriter;
import java.util.*;
import java.util.Map.Entry;

import genericutils.Err;
import genericutils.Id;
import genericutils.SimpleGraph;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.tc.TtspRecognizer;
import freeboogie.tc.TcInterface;

/**
 * Passify option.
 * Implements the algorithm found in the paper 
 * Avoiding Exponential Explosion: Generating Compact Verification Conditions
 * C. Flanagan and J. B. Saxe
 * 
 * 
 * @author J. Charles (julien.charles@gmail.com)
 */
public class Passificator extends ABasicPassifier {



  /** the main global environment. */
  private Environment fEnv;



  
  /**
   * Construct a passificator, relating to the current instance of the type checker.
   * @param tc the current system type checker
   * @param verbose triggers the statistics printing
   */
  public Passificator(TcInterface tc) {
    super(tc);
  }

  public Program process(Program program) {
    return new Program(
        process(program.ast, program.fileName), program.fileName);
  }

  /**
   * Process the AST, and returns the modified version.
   * @param ast the ast to look at.
   * @return a valid modified ast
   */
  public Declaration process(final Declaration ast, String fileName) {
    fEnv = new Environment(fileName);
    Declaration passifiedAst = (Declaration)ast.eval(this);
    
    if (false) { // TODO log-categ
      System.out.print(fEnv.globalToString());
    }
    passifiedAst = addVariableDeclarations(passifiedAst);
    verifyAst(passifiedAst);
    
    return getTypeChecker().getAST();
  }
  
  @Override
  public Ast eval(
    VariableDecl decl,
    Attribute attr,
    String name, 
    Type type,
    Identifiers typeVars,
    Declaration tail
  ) {
    fEnv.addGlobal(decl);
    Declaration newTail = tail != null?(Declaration)tail.eval(this) : null; 

    return VariableDecl.mk(null, name, type, typeVars, newTail);
  }
  
  @Override
  public Ast eval(
    Signature signature,
    String name, 
    Identifiers typeVars,
    Declaration args,
    Declaration results
  )  {
    return signature;
  }
  /**
   * Handles one implementation.
   */
  @Override
  public Implementation eval(
    Implementation implementation,
    Attribute attr,
    Signature sig,
    Body oldBody,
    Declaration tail
  ) {
    SimpleGraph<Block> currentFG = getTypeChecker().getFlowGraph(implementation);
    TtspRecognizer<Block> recog = new TtspRecognizer<Block>(currentFG, oldBody.getBlocks());
    Body body = oldBody;
    if (!recog.check()) {
      Err.warning(this + " " + implementation.loc() + ": Implementation " + 
        sig.getName() + " is not a series-parallel graph. I'm not passifying it.");
    } else if (currentFG.hasCycle()) {
      Err.warning(this + " " + implementation.loc() + ": Implementation " + 
        sig.getName() + " has cycles. I'm not passifying it.");
    } else {
      if (false) { // TODO log-categ
        System.out.println("process " + sig.getName());
      }
      BodyPassifier bp = BodyPassifier.passify(
        getTypeChecker(),
        fEnv, 
        oldBody,
        sig);
      sig = Signature.mk(
        sig.getName(), 
        sig.getTypeArgs(), 
        sig.getArgs(),
        bp.getResult(),
        sig.loc());
      body = bp.getBody();
      fEnv.updateGlobalWith(bp.getEnvironment());
    }

    // process the rest of the program
    if (tail != null) {
      tail = (Declaration)tail.eval(this);
    }
    return Implementation.mk(attr, sig, body, tail);
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
    if (!getTypeChecker().process(ast).isEmpty()) {
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
   * TODO: description.
   *
   * @author J. Charles (julien.charles@inria.fr)
   * @author reviewed by TODO
   */
  private static class BodyPassifier extends ABasicPassifier {
    /** the list of local variables declarations. */
    private Declaration newLocals = null;
    /** the current counter associated with each local variable. */
    private final Environment freshEnv;

    private final Map<Block, Environment> startBlockStatus = 
      new HashMap<Block, Environment> ();
    private final Map<Block, Environment> endBlockStatus = 
      new HashMap<Block, Environment> ();
    private final VariableDecl fResults;
    private SimpleGraph<Block> fFlowGraph;
    
    private Body fBody;
    private VariableDecl fNewResults;
    /**
     * Builds a body passifier.
     * @param typeChecker  
     * @param bIsVerbose
     * @param globalEnv 
     * @param sig */
    public BodyPassifier(
      final TcInterface typeChecker, 
      Environment globalEnv,
      final Signature sig
    ) {
      super(typeChecker);
      freshEnv = new Environment(sig.loc() + " " + sig.getName());
      fResults = (VariableDecl) sig.getResults();
      freshEnv.putAll(globalEnv);
      VariableDecl curr = (VariableDecl) sig.getArgs();
      while (curr != null) {
        freshEnv.put(curr, 0);
        curr = (VariableDecl) curr.getTail();
      }
    }
    
    public Environment getEnvironment() {
      return freshEnv;
    }

    public Body getBody() {
      return fBody;
    }

    public static BodyPassifier passify(
      TcInterface fTypeChecker,
      Environment globalEnv, 
      Body body,
      Signature sig
    ) {
      BodyPassifier bp = new BodyPassifier(fTypeChecker, globalEnv, sig);
      body.eval(bp);
      return bp;
    }

    private void computeDeclarations() {
      fNewResults = newResults(fResults);
      newLocals();
    }
    
    private void newLocals() {
      for (Entry<VariableDecl, Integer> decl: freshEnv.getLocalSet()) {
        int last = decl.getValue();
        VariableDecl old = decl.getKey();
        for (int i = 1; i <= last; ++i) {
          newLocals = mkDecl(old, i, newLocals);
        }
      }
    }
    
    private VariableDecl newResults(VariableDecl old) {
      if (old == null) return null;
      int last = freshEnv.get(old);
      freshEnv.remove(old);
      for (int i = 0; i < last; ++i) {
        newLocals = mkDecl(old, i, newLocals);
      }
      return mkDecl(old, last, newResults((VariableDecl)old.getTail()));
    }
  
    @Override
    public Ast eval(final Body body, Declaration vars, Block blocks) {
      // process out parameters
      newLocals = vars;
      VariableDecl curr = (VariableDecl) vars;
      while (curr != null) {
        freshEnv.put(curr, 0);
        curr = (VariableDecl) curr.getTail();
      }
      
      fFlowGraph = getTypeChecker().getFlowGraph(body);
      List<Block> list = fFlowGraph.nodesInTopologicalOrder();
      Iterator<Block> iter = list.iterator();
      Block newBlocks = evalBlock(iter.next(), iter);
      
      
      if (false) { // TODO log-categ
        System.out.print(freshEnv.localToString());
      }
      computeDeclarations();
      Body newBody = Body.mk(newLocals, newBlocks);
      fBody = newBody;
      return newBody;
    }
    


    public Block evalBlock(Block block, Iterator<Block> tail) {
      String name = block.getName();
      Command cmd = block.getCmd();
      Identifiers succ = block.getSucc();
      Set<Block> blist = fFlowGraph.from(block);
      Environment env = merge(blist);
      if (env == null) {
        env = freshEnv.clone();
      }
      
      startBlockStatus.put(block, env.clone()); 
      
      Command newCmd = cmd == null? null : (Command) cmd.eval(new CommandEvaluator(getTypeChecker(), env));
      endBlockStatus.put(block, env);  
      
      Block newTail = tail.hasNext()? evalBlock(tail.next(), tail) : null;
      
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
            String nodeName = Id.get(name);
            newTail = Block.mk(nodeName, assumeCmd, newSucc, newTail);
            newSucc = Identifiers.mk(AtomId.mk(nodeName, null), null);
          }
        }
      }
      freshEnv.updateWith(env);    

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
      
      Environment res = new Environment(freshEnv.getLoc());
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
          int newvar = freshEnv.get(decl) + 1;
          res.put(decl, newvar);
          freshEnv.put(decl, newvar);
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
    
    private class CommandEvaluator extends ABasicPassifier {
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
        Integer i = freshEnv.get(decl);
        int curr = i == null? 0 : i;
        curr++;
        env.put(decl, curr);
        freshEnv.put(decl, curr);
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
        if (decl == null) {
          // Symbol here!
          return mkVar(var, 0);
        }
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



}
