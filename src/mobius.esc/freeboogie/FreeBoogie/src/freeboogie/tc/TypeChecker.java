package freeboogie.tc;

import java.math.BigInteger;
import java.util.*;
import java.util.logging.Logger;

import genericutils.*;

import freeboogie.ErrorsFoundException;
import freeboogie.ast.*;
import freeboogie.astutil.TreeChecker;

/**
 * Typechecks an AST.
 *
 * In 'old mode' it uses {@code ForgivingStb} for building a
 * symbol table. 
 * 
 * It also acts more-or-less as a Facade for the whole package.
 *
 * NOTE subtyping is necessary only because of the special type
 * "any" which is likely to be ditched in the future.
 *
 * The typechecking works as follows. The eval functions associate
 * types to nodes in the AST that represent expressions. The check
 * functions ensure that type a can be used when type b is expected,
 * typically by checking the subtype relation. Comparing types
 * is done structurally. The strip function, called repetedly,
 * makes sure that `where' clauses are ignored.
 *
 * Type checking assumes that previous stages such as name resolution
 * (i.e., building of the symbo table) were successful.
 *
 * @author rgrig 
 * @see freeboogie.tc.ForgivingStb
 * @see freeboogie.tc.ForgivingTc
 */
@SuppressWarnings("unused") // many unused parameters
public class TypeChecker extends Evaluator<Type> implements TcInterface {

  private static final Logger log = Logger.getLogger("freeboogie.tc");
  
  // used for primitive types (so reference equality is used below)
  private PrimitiveType boolType, intType, refType;
  
  // used to signal an error in a subexpression and to limit
  // errors caused by other errors
  private PrimitiveType errType;
  
  private SymbolTable st;
  
  private GlobalsCollector gc;
  
  private BlockFlowGraphs flowGraphs;
  
  // detected errors
  private List<FbError> errors;
  
  // maps expressions to their types (caches the results of the
  // typechecker)
  private HashMap<Expr, Type> typeOf;
  
  // maps implementations to procedures
  private UsageToDefMap<Implementation, Procedure> implProc;
  
  // maps implementation params to procedure params
  private UsageToDefMap<VariableDecl, VariableDecl> paramMap;

  // maps type variables to their binding types
  private StackedHashMap<AtomId, Type> typeVar;

  // used for (randomized) union-find
  private static final Random rand = new Random(123);

  // implicitSpec.get(x) contains the mappings of type variables
  // to types that were inferred (and used) while type-checking x
  private Map<Ast, Map<AtomId, Type>> implicitSpec;

  // used as a stack of sets; this must be updated whenever
  // we decend into something parametrized by a generic type
  // that can contain expressions (e.g., functions, axioms,
  // procedure, implementation)
  private StackedHashMap<AtomId, AtomId> enclosingTypeVar;

  // accept deprecated constructs
  private boolean acceptOld;

  // records the last processed AST
  private Declaration ast;

  private int tvLevel; // DBG
  
  // === public interface ===
  
  /**
   * Make the typechecker accept deprecated constructs.
   */
  public void setAcceptOld(boolean acceptOld) {
    this.acceptOld = acceptOld;
  }

  @Override public Declaration getAST() { return ast; }

  /** 
   * Returns implicit specializations deduced/used by the typechecker
   * at various points in the AST. If later you want to check the
   * specialization performed for an ID then you should find the
   * mappings of type variables stored for ALL parents of the ID.
   */
  public Map<Ast, Map<AtomId, Type>> getImplicitSpec() {
    return implicitSpec;
  }
  
  // TODO: This appears verbatim in ForgivingTc.
  @Override public Program process(Program p) throws ErrorsFoundException {
    List<FbError> errors = process(p.ast);
    if (!errors.isEmpty()) throw new ErrorsFoundException(errors);
    return new Program(getAST(), p.fileName);
  }

  @Override
  public List<FbError> process(Declaration ast) {
    assert new TreeChecker().isTree(ast);

    tvLevel = 0; // DBG
    boolType = PrimitiveType.mk(PrimitiveType.Ptype.BOOL, -1);
    intType = PrimitiveType.mk(PrimitiveType.Ptype.INT, -1);
    refType = PrimitiveType.mk(PrimitiveType.Ptype.REF, -1);
    errType = PrimitiveType.mk(PrimitiveType.Ptype.ERROR, -1);
    
    typeOf = new HashMap<Expr, Type>();
    typeVar = new StackedHashMap<AtomId, Type>();
    implicitSpec = new HashMap<Ast, Map<AtomId, Type>>();
    enclosingTypeVar = new StackedHashMap<AtomId, AtomId>();
    
    // build symbol table
    StbInterface stb = acceptOld ? new ForgivingStb() : new SymbolTableBuilder();
    errors = stb.process(ast);
    if (!errors.isEmpty()) return errors;
    ast = stb.getAST();
    st = stb.getST();
    gc = stb.getGC();
    
    // check implementations
    ImplementationChecker ic = new ImplementationChecker();
    errors.addAll(ic.process(ast, gc));
    if (!errors.isEmpty()) return errors;
    implProc = ic.getImplProc();
    paramMap = ic.getParamMap();
    
    // check blocks
    flowGraphs = new BlockFlowGraphs();
    errors.addAll(flowGraphs.process(ast));
    if (!errors.isEmpty()) return errors;

    // do the typecheck
    ast.eval(this);
    this.ast = ast;
    return errors;
  }

  @Override
  public SimpleGraph<Block> getFlowGraph(Implementation impl) {
    return flowGraphs.getFlowGraph(impl.getBody());
  }
  @Override
  public SimpleGraph<Block> getFlowGraph(Body bdy) {
    return flowGraphs.getFlowGraph(bdy);
  }
  
  @Override
  public Map<Expr, Type> getTypes() {
    return typeOf;
  }
  
  @Override
  public UsageToDefMap<Implementation, Procedure> getImplProc() {
    return implProc;
  }
  
  @Override
  public UsageToDefMap<VariableDecl, VariableDecl> getParamMap() {
    return paramMap;
  }
  
  @Override
  public SymbolTable getST() {
    return st;
  }
  
  // === helper methods ===
  
  // ast may be used for debugging; it's here for symmetry
  private void typeVarEnter(Ast ast) { typeVar.push(); ++tvLevel; }
 
  private void typeVarExit(Ast ast) {
    Map<AtomId, Type> lis = new HashMap<AtomId, Type>();
    implicitSpec.put(ast, lis);
    for (Map.Entry<AtomId, Type> e : typeVar.peek().entrySet())
      if (!isTypeVar(e.getValue())) lis.put(e.getKey(), e.getValue());
    typeVar.pop();
    --tvLevel;
  }
  
  // assumes |d| is a list of |VariableDecl|
  // gives a TupleType with the types in that list
  private TupleType tupleTypeOfDecl(Declaration d) {
    if (d == null) return null;
    assert d instanceof VariableDecl;
    VariableDecl vd = (VariableDecl)d;
    return TupleType.mk(vd.getType(), tupleTypeOfDecl(vd.getTail()));
  }
  
  // strip DepType since only the prover can handle the where clauses
  // transform one element tuples into the types they contain
  private Type strip(Type t) {
    if (t instanceof DepType)
      return strip(((DepType)t).getType());
    else if (t instanceof TupleType) {
      TupleType tt = (TupleType)t;
      if (tt.getTail() == null) return strip(tt.getType());
    }
    return t;
  }
  
  // replaces all occurrences of UserType(a) with UserType(b) 
  private Type subst(Type t, String a, String b) {
    if (t instanceof UserType) {
      UserType tt = (UserType)t;
      if (tt.getName().equals(a)) return UserType.mk(b, null, tt.loc());
      return t;
    } else if (t instanceof MapType) {
      MapType tt = (MapType)t;
      return MapType.mk(
        (TupleType)subst(tt.getIdxType(), a, b),
        subst(tt.getElemType(), a, b),
        tt.loc());
    } else if (t instanceof IndexedType) {
      IndexedType tt = (IndexedType)t;
      return IndexedType.mk(
        subst(tt.getParam(), a, b),
        subst(tt.getType(), a, b),
        tt.loc());
    } else if (t instanceof DepType) {
      DepType tt = (DepType)t;
      return subst(tt.getType(), a, b);
    }
    assert t == null || t instanceof PrimitiveType;
    return t;
  }
  
  private boolean sub(PrimitiveType a, PrimitiveType b) {
    return a.getPtype() == b.getPtype();
  }
  
  private boolean sub(MapType a, MapType b) {
    if (!sub(b.getIdxType(), a.getIdxType())) return false;
    return sub(a.getElemType(), b.getElemType());
  }
  
  private boolean sub(UserType a, UserType b) {
    return a.getName().equals(b.getName());
  }
  
  private boolean sub(IndexedType a, IndexedType b) {
    if (!sub(a.getParam(), b.getParam()) || !sub(b.getParam(), a.getParam()))
      return false;
    return sub(a.getType(), b.getType());
  }
  
  private boolean sub(TupleType a, TupleType b) {
    if (!sub(a.getType(), b.getType())) return false;
    TupleType ta = a.getTail();
    TupleType tb = b.getTail();
    if (ta == tb) return true;
    if (ta == null ^ tb == null) return false;
    return sub(ta, tb);
  }

  // returns (a <: b)
  private boolean sub(Type a, Type b) {
    // get rid of where clauses strip () if only one type inside
    a = strip(a); b = strip(b);
    
    if (a == b) return true; // the common case
    if (a == errType || b == errType) return true; // don't trickle up errors
    
    // an empty tuple is only the same with an empty tuple
    if (a == null ^ b == null) return false;
    
    // check if b is ANY
    if (b instanceof PrimitiveType) {
      PrimitiveType sb = (PrimitiveType)b;
      if (sb.getPtype() == PrimitiveType.Ptype.ANY) return true;
    }

    // handle type variables
    a = realType(a);
    b = realType(b);
    if (isTypeVar(a) || isTypeVar(b)) {
      equalTypeVar(a, b);
      return true;
    }

    // compatibility stuff, to be run only in "old" mode
    if (acceptOld) {
      // allow <X>T to be used where T is expected if in "old" mode
      if (a instanceof IndexedType && !(b instanceof IndexedType)) {
        IndexedType it = (IndexedType)a;
        if (sub(it.getType(), b)) return true;
      }

      // allow "name" where "<*>name" is expected
      if (a instanceof PrimitiveType && b instanceof IndexedType) {
        PrimitiveType apt = (PrimitiveType)a;
        IndexedType it = (IndexedType)b;
        Type bt = it.getType();
        if (apt.getPtype() == PrimitiveType.Ptype.NAME && bt instanceof PrimitiveType) {
          PrimitiveType bpt = (PrimitiveType)bt;
          if (bpt.getPtype() == PrimitiveType.Ptype.NAME) return true;
        }
      }
    }
    
    // the main check
    if (a instanceof PrimitiveType && b instanceof PrimitiveType)
      return sub((PrimitiveType)a, (PrimitiveType)b);
    else if (a instanceof MapType && b instanceof MapType)
      return sub((MapType)a, (MapType)b);
    else if (a instanceof UserType && b instanceof UserType) 
      return sub((UserType)a, (UserType)b);
    else if (a instanceof IndexedType && b instanceof IndexedType)
      return sub((IndexedType)a, (IndexedType)b);
    else if (a instanceof TupleType && b instanceof TupleType)
      return sub((TupleType)a, (TupleType)b);
    else
      return false;
  }

  private void collectEnclosingTypeVars(Identifiers ids) {
    if (ids == null) return;
    enclosingTypeVar.put(ids.getId(), ids.getId());
    collectEnclosingTypeVars(ids.getTail());
  }

  private Type realType(Type t) {
    AtomId ai;
    Type nt;
    while (true) {
      ai = getTypeVarDecl(t);
      if (ai == null || (nt = typeVar.get(ai)) == null) break;
      typeVar.put(ai, nt);
      t = nt;
    }
    return t;
  }

  /* Substitutes real types for (known) type variables.
   * If the result is a type variable then an error is reported
   * at location {@code loc}.
   */
  private Type checkRealType(Type t, Ast l) {
    t = substRealType(t);
    if (isTypeVar(t)) {
      errors.add(new FbError(FbError.Type.REQ_SPECIALIZATION, l,
            TypeUtils.typeToString(t), t.loc(), getTypeVarDecl(t)));
      t = errType;
    }
    return t;
  }

  /* Changes all occurring type variables in {@code t} into
   * the corresponding real types.
   */
  private Type substRealType(Type t) {
    if (t == null) return null;
    if (t instanceof TupleType) {
      TupleType tt = (TupleType)t;
      return TupleType.mk(
          substRealType(tt.getType()), 
          (TupleType)substRealType(tt.getTail()));
    } else if (t instanceof MapType) {
      MapType at = (MapType)t;
      return MapType.mk(
          (TupleType)substRealType(at.getIdxType()),
          substRealType(at.getElemType()));
    } else if (t instanceof IndexedType) {
      IndexedType it = (IndexedType)t;
      return IndexedType.mk(
          substRealType(it.getParam()),
          substRealType(it.getType()));
    } else if (t instanceof DepType) {
      DepType dt = (DepType)t;
      return DepType.mk(substRealType(dt.getType()), dt.getPred());
    }
    Type nt = realType(t);
    return nt;
  }

  private boolean isTypeVar(Type t) {
    AtomId ai = getTypeVarDecl(t);
    return ai != null && enclosingTypeVar.get(ai) == null;
  }

  private AtomId getTypeVarDecl(Type t) {
    if (!(t instanceof UserType)) return null;
    return st.typeVars.def((UserType)t);
  }

  // pre: |a| and |b| are as 'real' as possible
  private void equalTypeVar(Type a, Type b) {
    assert !isTypeVar(a) || !typeVar.containsKey(getTypeVarDecl(a));
    assert !isTypeVar(b) || !typeVar.containsKey(getTypeVarDecl(b));
    if (!isTypeVar(a) && !isTypeVar(b)) {
      assert TypeUtils.eq(a, b);
      return;
    }
    if (!isTypeVar(a) || (isTypeVar(b)  && rand.nextBoolean())) {
      Type t = a; a = b; b = t;
    }
    AtomId ai = getTypeVarDecl(a);
    if (getTypeVarDecl(b) != ai) {
      log.fine("TC: typevar " + ai.getId() + "@" + ai.loc() +
        " == type " + TypeUtils.typeToString(b));
      assert tvLevel > 0; // ypu probably need to add typeVarEnter/Exit in some places
      typeVar.put(ai, b);
    }
  }

  private void mapExplicitGenerics(Identifiers tv, TupleType t) {
    if (t == null) return;
    if (tv == null) {
      errors.add(new FbError(FbError.Type.GEN_TOOMANY, t));
      return;
    }
    assert tvLevel > 0;
    typeVar.put(tv.getId(), t.getType());
    mapExplicitGenerics(tv.getTail(), t.getTail());
  }
  
  /**
   * If {@code a} cannot be used where {@code b} is expected then an error
   * at location {@code l} is produced and {@code errors} is set.
   */
  private void check(Type a, Type b, Ast l) {
    if (sub(a, b)) return;
    errors.add(new FbError(FbError.Type.NOT_SUBTYPE, l,
          TypeUtils.typeToString(a), TypeUtils.typeToString(b)));
  }
  
  /**
   * Same as {@code check}, except it is more picky about the types:
   * They must be exactly the same.
   */
  private void checkExact(Type a, Type b, Ast l) {
    // BUG? Should || be &&?
    if (sub(a, b) || sub(b, a)) return;
    errors.add(new FbError(FbError.Type.BAD_TYPE, l,
          TypeUtils.typeToString(a), TypeUtils.typeToString(b)));
  }

  // === visiting operators ===
  @Override
  public PrimitiveType eval(UnaryOp unaryOp, UnaryOp.Op op, Expr e) {
    Type t = strip(e.eval(this));
    switch (op) {
    case MINUS:
      check(t, intType, e);
      typeOf.put(unaryOp, intType);
      return intType;
    case NOT:
      check(t, boolType, e);
      typeOf.put(unaryOp, boolType);
      return boolType;
    default:
      assert false;
      return null; // dumb compiler
    }
  }

  @Override
  public PrimitiveType eval(BinaryOp binaryOp, BinaryOp.Op op, Expr left, Expr right) {
    Type l = strip(left.eval(this));
    Type r = strip(right.eval(this));
    switch (op) {
    case PLUS:
    case MINUS:
    case MUL:
    case DIV:
    case MOD:
      // integer arguments and integer result
      check(l, intType, left);
      check(r, intType, right);
      typeOf.put(binaryOp, intType);
      return intType;
    case LT:
    case LE:
    case GE:
    case GT:
      // integer arguments and boolean result
      check(l, intType, left);
      check(r, intType, right);
      typeOf.put(binaryOp, boolType);
      return boolType;
    case EQUIV:
    case IMPLIES:
    case AND:
    case OR:
      // boolean arguments and boolean result
      check(l, boolType, left);
      check(r, boolType, right);
      typeOf.put(binaryOp, boolType);
      return boolType;
    case SUBTYPE:
      // l subtype of r and boolean result (TODO: a user type is a subtype of a user type)
      check(l, r, left);
      typeOf.put(binaryOp, boolType);
      return boolType;
    case EQ:
    case NEQ:
      // typeOf(l) == typeOf(r) and boolean result
      typeVarEnter(binaryOp);
      checkExact(l, r, binaryOp);
      typeVarExit(binaryOp);
      typeOf.put(binaryOp, boolType);
      return boolType;
    default:
      assert false;
      return errType; // dumb compiler
    }
  }
  
  // === visiting atoms ===
  @Override
  public Type eval(AtomId atomId, String id, TupleType types) {
    Declaration d = st.ids.def(atomId);
    Type t = errType;
    if (d instanceof VariableDecl) {
      VariableDecl vd = (VariableDecl)d;
      typeVarEnter(atomId);
      mapExplicitGenerics(vd.getTypeArgs(), types);
      t = checkRealType(vd.getType(), atomId);
      typeVarExit(atomId);
    } else if (d instanceof ConstDecl) {
      assert types == null; // TODO
      t = ((ConstDecl)d).getType();
    } else assert false;
    typeOf.put(atomId, t);
    return t;
  }

  @Override
  public PrimitiveType eval(AtomNum atomNum, BigInteger val) {
    typeOf.put(atomNum, intType);
    return intType;
  }

  @Override
  public PrimitiveType eval(AtomLit atomLit, AtomLit.AtomType val) {
    switch (val) {
    case TRUE:
    case FALSE:
      typeOf.put(atomLit, boolType);
      return boolType;
    case NULL:
      typeOf.put(atomLit, refType);
      return refType;
    default:
      assert false;
      return errType; // dumb compiler 
    }
  }

  @Override
  public Type eval(AtomOld atomOld, Expr e) {
    Type t = e.eval(this);
    typeOf.put(atomOld, t);
    return t;
  }

  @Override
  public PrimitiveType eval(
    AtomQuant atomQuant,
    AtomQuant.QuantType quant,
    Declaration vars,
    Attribute attr,
    Expr e
  ) {
    Type t = e.eval(this);
    check(t, boolType, e);
    typeOf.put(atomQuant, boolType);
    return boolType;
  }

  @Override
  public Type eval(AtomFun atomFun, String function, TupleType types, Exprs args) {
    FunctionDecl d = st.funcs.def(atomFun);
    Signature sig = d.getSig();
    Declaration fargs = sig.getArgs();
    
    typeVarEnter(atomFun);
    mapExplicitGenerics(sig.getTypeArgs(), types);
    Type at = strip(args == null? null : (TupleType)args.eval(this));
    Type fat = strip(tupleTypeOfDecl(fargs));
   
    check(at, fat, args == null? atomFun : args);
    Type rt = strip(checkRealType(
          tupleTypeOfDecl(sig.getResults()), atomFun));
    typeVarExit(atomFun);
    typeOf.put(atomFun, rt);
    return rt;
  }

  @Override
  public Type eval(AtomCast atomCast, Expr e, Type type) {
    e.eval(this);
    typeOf.put(atomCast, type);
    return type;
  }

  @Override
  public Type eval(AtomMapSelect atomMapSelect, Atom atom, Exprs idx) {
    Type t = strip(atom.eval(this));
    if (t == errType) return errType;
    if (!(t instanceof MapType)) {
      errors.add(new FbError(FbError.Type.NEED_ARRAY, atom));
      return errType;
    }
    MapType at = (MapType)t;

    // look at indexing types
    typeVarEnter(atomMapSelect);
    check(idx.eval(this), at.getIdxType(), idx);
    Type et = checkRealType(at.getElemType(), atomMapSelect);
    typeVarExit(atomMapSelect);
    typeOf.put(atomMapSelect, et);
    return et;
  }
  
  @Override
  public Type eval(AtomMapUpdate atomMapUpdate, Atom atom, Exprs idx, Expr val) {
    typeVarEnter(atomMapUpdate);
    Type t = strip(atom.eval(this));
    Type ti = strip(idx.eval(this));
    Type tv = strip(val.eval(this));
    if (t == errType || ti == errType || tv == errType) return errType;
    MapType mt;
    if (!(t instanceof MapType)) {
      errors.add(new FbError(FbError.Type.NEED_ARRAY, atom));
      typeVarExit(atomMapUpdate);
      return errType;
    }
    mt = (MapType)t;
    check(idx.eval(this), mt.getIdxType(), idx);
    check(tv, mt.getElemType(), val);
    typeVarExit(atomMapUpdate);
    typeOf.put(atomMapUpdate, mt);
    return mt;
  }

  // === visit commands ===
  @Override
  public Type eval(AssignmentCmd assignmentCmd, AtomId lhs, Expr rhs) {
    Type lt = strip(lhs.eval(this));
    Type rt = strip(rhs.eval(this));
    typeVarEnter(assignmentCmd);
    check(rt, lt, assignmentCmd);
    typeVarExit(assignmentCmd);
    return null;
  }

  @Override
  public Type eval(AssertAssumeCmd assertAssumeCmd, AssertAssumeCmd.CmdType type, Identifiers typeVars, Expr expr) {
    enclosingTypeVar.push();
    collectEnclosingTypeVars(typeVars);
    Type t = expr.eval(this);
    check(t, boolType, assertAssumeCmd);
    enclosingTypeVar.pop();
    return null;
  }

  @Override
  public Type eval(CallCmd callCmd, String procedure, TupleType types, Identifiers results, Exprs args) {
    Procedure p = st.procs.def(callCmd);
    Signature sig = p.getSig();
    Declaration fargs = sig.getArgs();

    typeVarEnter(callCmd);
    
    // check the actual arguments against the formal ones
    Type at = strip(args == null? null : args.eval(this));
    Type fat = strip(tupleTypeOfDecl(fargs));
    check(at, fat, args == null? callCmd : args);
    
    // check the assignment of the results
    Type lt = strip(results == null? null : results.eval(this));
    Type rt = strip(tupleTypeOfDecl(sig.getResults()));
    check(rt, lt, callCmd);

    typeVarExit(callCmd);
    
    return null;
  }
  
  // === visit dependent types ===
  @Override
  public DepType eval(DepType depType, Type type, Expr pred) {
    Type t = pred.eval(this);
    check(t, boolType, pred);
    return null;
  }
  
  // === visit Exprs and Identifiers to make TupleType-s ===
  @Override
  public TupleType eval(Exprs exprs, Expr expr, Exprs tail) {
    Type t = expr.eval(this);
    assert t != null; // shouldn't have nested tuples
    TupleType tt = tail == null? null : (TupleType)tail.eval(this);
    TupleType rt = TupleType.mk(t, tt);
    typeOf.put(exprs, rt);
    return rt;
  }

  @Override
  public TupleType eval(Identifiers identifiers, AtomId id, Identifiers tail) {
    Type t = id.eval(this);
    TupleType tt = tail == null? null : (TupleType)tail.eval(this);
    TupleType rt = TupleType.mk(t, tt);
    // TODO: put this in typeOf?
    return rt;
  }
  
  // === visit various things that must have boolean params ===
  @Override
  public Type eval(Specification specification, Identifiers tv, Specification.SpecType type, Expr expr, boolean free, Specification tail) {
    enclosingTypeVar.push();
    collectEnclosingTypeVars(tv);
    Type t = null;
    switch (type) {
    case REQUIRES:
    case ENSURES:
      t = expr.eval(this);
      check(t, boolType, expr);
      break;
    case MODIFIES:
      break;
    default:
      assert false;
      return errType; // dumb compiler
    }
    enclosingTypeVar.pop();
    if (tail != null) tail.eval(this);
    return null;
  }

  @Override
  public Type eval(
    Axiom axiom,
    Attribute attr, 
    String name,
    Identifiers typeVars,
    Expr expr,
    Declaration tail
  ) {
    enclosingTypeVar.push();
    collectEnclosingTypeVars(typeVars);
    Type t = expr.eval(this);
    check(t, boolType, expr);
    enclosingTypeVar.pop();
    if (tail != null) tail.eval(this);
    return null;
  }

  // === keep track of formal generics (see also eval(Axiom...) and eval(AssertAssumeCmd...)) ===
  @Override
  public Type eval(
    FunctionDecl function,
    Attribute attr,
    Signature sig,
    Declaration tail
  ) {
    if (tail != null) tail.eval(this);
    return null;
  }

  @Override
  public Type eval(
    VariableDecl variableDecl,
    Attribute attr, 
    String name,
    Type type,
    Identifiers typeVars,
    Declaration tail
  ) {
    if (tail != null) tail.eval(this);
    return null;
  }

  @Override
  public Type eval(
    Procedure procedure,
    Attribute attr, 
    Signature sig,
    Specification spec,
    Declaration tail
  ) {
    enclosingTypeVar.push();
    collectEnclosingTypeVars(sig.getTypeArgs());
    if (spec != null) spec.eval(this);
    enclosingTypeVar.pop();
    if (tail != null) tail.eval(this);
    return null;
  }

  @Override
  public Type eval(
    Implementation implementation,
    Attribute attr,
    Signature sig,
    Body body,
    Declaration tail
  ) {
    enclosingTypeVar.push();
    collectEnclosingTypeVars(sig.getTypeArgs());
    body.eval(this);
    enclosingTypeVar.pop();
    if (tail != null) tail.eval(this);
    return null;
  }

  // === do not look at block successors ===
  @Override
  public Type eval(Block block, String name, Command cmd, Identifiers succ, Block tail) {
    if (cmd != null) cmd.eval(this);
    if (tail != null) tail.eval(this);
    return null;
  }
}
