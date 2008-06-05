package freeboogie.tc;

import java.util.logging.Logger;
import java.util.*;

import freeboogie.ast.*;

/**
 * Builds a symbol table for a given AST, perhaps modifying
 * the AST slightly so that name resolution errors are
 * eliminated.
 *
 * The only modification that this class does at this time
 * is to introduce generics (type variables) on the innermost
 * declaration that contains a (type-) name error. For example,
 * the variable declaration {@code var h : [ref,&lt;x&gt;name]x}
 * is transformed into {@code var h&lt;x&gt; : [ref,&lt;x&gt;name]x}.
 */
public class ForgivingStb extends Transformer implements StbInterface {

  private static final Logger log = Logger.getLogger("freeboogie.tc"); 
  
  // does the real work
  private StbInterface stb;

  private Set<UserType> undeclIds;

  // used to collect the local undeclared ids
  private Set<String> toIntroduce;

  /**
   * Constructs a forgiving symbol table builder.
   */
  public ForgivingStb() {
    stb = new SymbolTableBuilder();
  }

  @Override
  public GlobalsCollector getGC() { return stb.getGC(); }

  @Override
  public SymbolTable getST() { return stb.getST(); }

  @Override
  public Declaration getAST() { return stb.getAST(); }

  @Override
  public List<FbError> process(Declaration ast) {
    int oldErrCnt = Integer.MAX_VALUE;
    List<FbError> errors;
    while (true) {
      errors = stb.process(ast);
      int errCnt = errors.size();
      if (errCnt >= oldErrCnt || errCnt == 0) break;
      oldErrCnt = errCnt;
      ast = fix(ast, errors);
      log.info("Running SymbolTableBuilder again.");
    }
    return errors;
  }

  /*
   * This relies on FbError UNDECL_ID to point to AtomId as
   * the location of the error.
   */
  private Declaration fix(Declaration ast, List<FbError> errors) {
    undeclIds = new HashSet<UserType>();
    for (FbError e : errors) {
      switch (e.type()) {
      case UNDECL_ID:
        Ast l = e.place();
        if (l instanceof UserType) undeclIds.add((UserType)l);
        break;
      default:
        /* do nothing */
      }
    }
    toIntroduce = new HashSet<String>();
    return (Declaration)ast.eval(this);
  }

  // === identify problematic places ===
  @Override
  public void see(UserType userType, String name) {
    if (!undeclIds.contains(userType)) return;
    assert name != null;
    toIntroduce.add(name);
    log.finer("record undecl usertype " + name);
  }
  
  // === do corrections, if needed ===
  // TODO Refactor
  // TODO Optimize for the common case when there are no changes
  @Override
  public VariableDecl eval(VariableDecl variableDecl, String name, Type type, Identifiers typeVars, Declaration tail) {
    assert toIntroduce.isEmpty();
    type = (Type)type.eval(this);
    for (String ti : toIntroduce) {
      typeVars = Identifiers.mk(AtomId.mk(ti, null), typeVars);
      log.fine("Introducing " + ti + " as a generic on var " + name);
    }
    toIntroduce.clear();
    if (tail != null) tail = (Declaration)tail.eval(this);
    return VariableDecl.mk(name, type, typeVars, tail, variableDecl.loc());
  }

  @Override
  public Axiom eval(Axiom axiom, Identifiers typeVars, Expr expr, Declaration tail) {
    assert toIntroduce.isEmpty();
    expr = (Expr)expr.eval(this);
    for (String ti : toIntroduce) {
      typeVars = Identifiers.mk(AtomId.mk(ti, null), typeVars);
      log.fine("Introducing " + ti + " as a generic on axiom at " + axiom.loc());
    }
    toIntroduce.clear();
    if (tail != null) tail = (Declaration)tail.eval(this);
    return Axiom.mk(typeVars, expr, tail, axiom.loc());
  }

  @Override
  public Signature eval(Signature signature, String name, Declaration args, Declaration results, Identifiers typeVars) {
    assert toIntroduce.isEmpty();
    if (args != null) args = (Declaration)args.eval(this);
    if (results != null) results = (Declaration)results.eval(this);
    for (String ti : toIntroduce) {
      typeVars = Identifiers.mk(AtomId.mk(ti, null), typeVars);
      log.fine("Introducing " + ti + " as a generic on sig " + name);
    }
    toIntroduce.clear();
    return Signature.mk(name, args, results, typeVars, signature.loc());
  }

  @Override
  public Specification eval(Specification specification, Identifiers typeVars, Specification.SpecType type, Expr expr, boolean free, Specification tail) {
    assert toIntroduce.isEmpty();
    expr = (Expr)expr.eval(this);
    for (String ti : toIntroduce) {
      typeVars = Identifiers.mk(AtomId.mk(ti, null), typeVars);
      log.fine("Introducing " + ti + " as a generic to spec at " + specification.loc());
    }
    toIntroduce.clear();
    if (tail != null) tail = (Specification)tail.eval(this);
    return Specification.mk(typeVars, type, expr, free, tail, specification.loc());
  }

}

