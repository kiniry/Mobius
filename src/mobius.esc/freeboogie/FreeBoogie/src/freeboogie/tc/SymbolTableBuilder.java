package freeboogie.tc;

import java.util.*;

import genericutils.StackedHashMap;

import freeboogie.ast.*;

/**
 * Constructs a {@code SymbolTable} from an AST.
 *
 * TODO(rgrig): Compute map axiom_name <-> axiom
 * 
 * @author rgrig 
 * @author miko
 */
@SuppressWarnings("unused") // lots of unused parameters
public class SymbolTableBuilder extends Transformer implements StbInterface {
  private StackedHashMap<String, VariableDecl> localVarDecl;
  private StackedHashMap<String, AtomId> typeVarDecl;

  private Declaration ast;
  private SymbolTable symbolTable;
  private GlobalsCollector gc;
  
  // problems found while building the symbol table 
  private List<FbError> errors;
  
  // for modifies spec we ignore the arguments
  private boolean lookInLocalScopes;
  
  /**
   * Builds a symbol table. Reports name clashes (because it
   * uses {@code GlobalsCollector}. Reports undeclared variables.
   * @param ast the AST to analyze
   * @return a list with the problems detected
   */
  @Override
  public List<FbError> process(Declaration ast) {
    localVarDecl = new StackedHashMap<String, VariableDecl>();
    typeVarDecl = new StackedHashMap<String, AtomId>();
    symbolTable = new SymbolTable();
    gc = new GlobalsCollector();
    lookInLocalScopes = true;
    errors = gc.process(ast);
    ast.eval(this);
    this.ast = ast;
    return errors;
  }

  @Override
  public Declaration getAST() {
    return ast;
  }

  /**
   * Returns the symbol table.
   * @return the symbol table
   */
  @Override
  public SymbolTable getST() {
    return symbolTable;
  }
  
  /**
   * Returns the globals collector, which can be used to resolve global names.
   * @return the globals collector
   */
  @Override
  public GlobalsCollector getGC() {
    return gc;
  }
  
  // === helpers ===
  
  // reports an error at location l if d is null
  private <T> T check(T d, String s, Ast l) {
    if (d != null) return d;
    errors.add(new FbError(FbError.Type.UNDECL_ID, l, s));
    return null;
  }
  
  // the return might by ConstDecl or VariableDecl
  private Declaration lookup(String s, Ast l) {
    Declaration r = localVarDecl.get(s);
    if (r == null) r = gc.idDef(s);
    return check(r, s, l);
  }

  private void collectTypeVars(Map<String, AtomId> tv, Identifiers ids) {
    if (ids == null) return;
    AtomId a = ids.getId();
    String n = a.getId();
    if (tv.get(n) != null)
      errors.add(new FbError(FbError.Type.TV_ALREADY_DEF, a, a.getId()));
    symbolTable.typeVars.seenDef(ids.getId());
    typeVarDecl.put(n, a);
    collectTypeVars(tv, ids.getTail());
  }
  
  // === visit methods ===
  
  @Override
  public void see(UserType userType, String name, TupleType typeArgs) {
    AtomId tv = typeVarDecl.get(name);
    if (tv != null)
      symbolTable.typeVars.put(userType, tv);
    else
      symbolTable.types.put(userType, check(gc.typeDef(name), name, userType));
  }

  @Override
  public void see(CallCmd callCmd, String p, TupleType types, Identifiers results, Exprs args) {
    symbolTable.procs.put(callCmd, check(gc.procDef(p), p, callCmd));
    if (types != null) types.eval(this);
    if (results != null) results.eval(this);
    if (args != null) args.eval(this);
  }

  @Override
  public void see(AtomFun atomFun, String f, TupleType types, Exprs args) {
    symbolTable.funcs.put(atomFun, check(gc.funDef(f), f, atomFun));
    if (types != null) types.eval(this);
    if (args != null) args.eval(this);
  }

  @Override
  public void see(AtomId atomId, String id, TupleType types) {
    symbolTable.ids.put(atomId, lookup(id, atomId));
    if (types != null) types.eval(this);
  }

  // === collect info from local scopes ===
  @Override
  public void see(
    VariableDecl variableDecl,
    Attribute attr,
    String name,
    Type type,
    Identifiers typeVars,
    Declaration tail
  ) {
    symbolTable.ids.seenDef(variableDecl);
    typeVarDecl.push();
    collectTypeVars(typeVarDecl.peek(), typeVars);
    Map<String, VariableDecl> scope = localVarDecl.peek();
    if (localVarDecl.frames() > 0 && name != null) {
      // we are in a local scope
      VariableDecl old = scope.get(name);
      if (old != null)
        errors.add(new FbError(FbError.Type.ALREADY_DEF, variableDecl, name));
      else 
        scope.put(name, variableDecl);
    }
    type.eval(this);
    typeVarDecl.pop();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(
    ConstDecl constDecl,
    Attribute attr,
    String id,
    Type type,
    boolean uniq,
    Declaration tail
  ) {
    symbolTable.ids.seenDef(constDecl);
    type.eval(this);
    if (tail != null) tail.eval(this);
  }
  
  @Override
  public void see(
    Signature signature,
    String name,
    Identifiers typeArgs,
    Declaration args,
    Declaration results
  ) {
    collectTypeVars(typeVarDecl.peek(), typeArgs);
    if (args != null) args.eval(this);
    if (results != null) results.eval(this);
  }

  
  // === keep track of local scopes ===
  @Override
  public void see(
    Procedure procedure,
    Attribute attr,
    Signature sig,
    Specification spec,
    Declaration tail
  ) {
    symbolTable.procs.seenDef(procedure);
    localVarDecl.push();
    typeVarDecl.push();
    sig.eval(this);
    if (spec != null) spec.eval(this);
    typeVarDecl.pop();
    localVarDecl.pop();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(
    Implementation implementation,
    Attribute attr,
    Signature sig,
    Body body,
    Declaration tail
  ) {
    localVarDecl.push();
    typeVarDecl.push();
    sig.eval(this);
    body.eval(this);
    typeVarDecl.pop();
    localVarDecl.pop();
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(
    FunctionDecl function,
    Attribute attr,
    Signature sig,
    Declaration tail
  ) {
    symbolTable.funcs.seenDef(function);
    typeVarDecl.push();
    sig.eval(this);
    typeVarDecl.pop();
    if (tail != null) tail.eval(this);
  }
  
  @Override
  public void see(
    AtomQuant atomQuant,
    AtomQuant.QuantType quant,
    Declaration vars,
    Attribute attr,
    Expr e
  ) {
    localVarDecl.push();
    vars.eval(this);
    if (attr != null) attr.eval(this);
    e.eval(this);
    localVarDecl.pop();
  }
  
  @Override
  public void see(
    Axiom axiom,
    Attribute attr, 
    String name,
    Identifiers typeArgs,
    Expr expr,
    Declaration tail
  ) {
    typeVarDecl.push();
    collectTypeVars(typeVarDecl.peek(), typeArgs);
    expr.eval(this);
    typeVarDecl.pop();
    if (tail != null) tail.eval(this);
  }
  
  @Override
  public void see(AssertAssumeCmd assertAssumeCmd, AssertAssumeCmd.CmdType type, Identifiers typeVars, Expr expr) {
    typeVarDecl.push();
    collectTypeVars(typeVarDecl.peek(), typeVars);
    expr.eval(this);
    typeVarDecl.pop();
  }
  
  // === remember if we are below a modifies spec ===
  
  @Override
  public void see(Specification specification, Identifiers tv, Specification.SpecType type, Expr expr, boolean free, Specification tail) {
    typeVarDecl.push();
    collectTypeVars(typeVarDecl.peek(), tv);
    if (type == Specification.SpecType.MODIFIES) {
      assert lookInLocalScopes; // no nesting
      lookInLocalScopes = false;
    }
    expr.eval(this);
    lookInLocalScopes = true;
    typeVarDecl.pop();
    if (tail != null) tail.eval(this);
  }
  
  
  // === do not look at goto-s ===
  @Override
  public void see(Block block, String name, Command cmd, Identifiers succ, Block tail) {
    if (cmd != null) cmd.eval(this);
    if (tail != null) tail.eval(this);
  }
}
