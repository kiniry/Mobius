/** Public domain. */

package freeboogie.tc;

import java.util.HashMap;
import java.util.LinkedList;

import freeboogie.ast.*;
import freeboogie.util.Err;

/**
 * Constructs a {@code SymbolTable} from an AST.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
@SuppressWarnings("unused") // lots of unused parameters
public class SymbolTableBuilder extends Transformer {
  private LinkedList<HashMap<String, VariableDecl>> localScopes;
  
  private SymbolTable symbolTable;
  
  private GlobalsCollector gc;
  
  private boolean errors;
  
  /**
   * Builds a symbol table. Reports name clashes (because it
   * uses {@code GlobalsCollector}. Reports undeclared variables.
   * @param ast the AST to analyze
   * @return whether there were any problems detected
   */
  public boolean process(Declaration ast) {
    errors = false;
    localScopes = new LinkedList<HashMap<String, VariableDecl>>();
    symbolTable = new SymbolTable();
    gc = new GlobalsCollector();
    boolean e = gc.process(ast);
    ast.eval(this);
    return errors || e;
  }

  /**
   * Returns the symbol table.
   * @return the symbol table
   */
  public SymbolTable getST() {
    return symbolTable;
  }
  
  // === helpers ===
  
  // reports an error at location l if d s null
  private <T> T check(T d, String s, AstLocation l) {
    if (d != null) return d;
    Err.error("" + l + ": Undeclared identifier " + s + ".");
    errors = true;
    return null;
  }
  
  // the return might by ConstDecl or VariableDecl
  private Declaration lookup(String s, AstLocation l) {
    for (HashMap<String, VariableDecl> scope : localScopes) {
      VariableDecl d = scope.get(s);
      if (d != null) return d;
    }
    return check(gc.idDef(s), s, l);
  }
  
  // === visit methods ===
  
  // Grr, why doesn't Java have functions as parameters or at least macros?
  
  @Override
  public void see(UserType userType, String name) {
    symbolTable.types.put(userType, check(gc.typeDef(name), name, userType.loc()));
  }

  @Override
  public void see(CallCmd callCmd, String p, Identifiers results, Exprs args) {
    symbolTable.procs.put(callCmd, check(gc.procDef(p), p, callCmd.loc()));
    if (results != null) results.eval(this);
    if (args != null) args.eval(this);
  }

  @Override
  public void see(AtomFun atomFun, String f, Exprs args) {
    symbolTable.funcs.put(atomFun, check(gc.funDef(f), f, atomFun.loc()));
    if (args != null) args.eval(this);
  }

  @Override
  public void see(AtomId atomId, String id) {
    symbolTable.ids.put(atomId, lookup(id, atomId.loc()));
  }

  // === collect info from local scopes ===
  @Override
  public void see(VariableDecl variableDecl, String name, Type type, Declaration tail) {
    HashMap<String, VariableDecl> scope = localScopes.peekFirst();
    if (scope != null) {
      // we are in a local scope
      scope.put(name, variableDecl);
    }
    if (tail != null) tail.eval(this);
  }
  
  // === keep track of local scopes ===
  @Override
  public void see(Procedure procedure, Signature sig, Specification spec, Body body, Declaration tail) {
    HashMap<String, VariableDecl> newScope = new HashMap<String, VariableDecl>();
    localScopes.addFirst(newScope);
    sig.eval(this);
    if (spec != null) spec.eval(this);
    if (body != null) body.eval(this);
    localScopes.removeFirst();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(Implementation implementation, Signature sig, Body body, Declaration tail) {
    HashMap<String, VariableDecl> newScope = new HashMap<String, VariableDecl>();
    localScopes.addFirst(newScope);
    sig.eval(this);
    body.eval(this);
    localScopes.removeFirst();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(AtomQuant atomQuant, AtomQuant.QuantType quant, Declaration vars, Trigger trig, Expr e) {
    HashMap<String, VariableDecl> newScope = new HashMap<String, VariableDecl>();
    localScopes.addFirst(newScope);
    vars.eval(this);
    if (trig != null) trig.eval(this);
    e.eval(this);
    localScopes.removeFirst();
  }
  
  // === don't look at goto's ===
  @Override
  public void see(BlockEnd blockEnd, BlockEnd.BlockType type, Identifiers dest) {
    // do nothing
  }

}
