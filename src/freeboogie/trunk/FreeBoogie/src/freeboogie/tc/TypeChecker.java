package freeboogie.tc;

import java.io.StringWriter;
import java.math.BigInteger;
import java.util.*;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.util.Closure;
import freeboogie.util.Err;
import freeboogie.util.StackedHashMap;

/**
 * Typechecks an AST. Errors are reported using the class {@code Err}.
 * It maps expressions to types.
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
 * @author reviewed by TODO
 */
@SuppressWarnings("unused") // many unused parameters
public class TypeChecker extends Evaluator<Type> {
  // used for primitive types (so reference equality is used below)
  private PrimitiveType boolType, intType, refType, nameType, anyType;
  
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

  // used as a stack of sets; this must be updated whenever
  // we decend into something parametrized by a generic type
  // that can contain expressions (e.g., functions, axioms,
  // procedure, implementation)
  private StackedHashMap<AtomId, AtomId> enclosingTypeVar;

  // accept deprecated constructs
  private boolean acceptOld;
  
  // === public interface ===
  
  /**
   * Make the typechecker accept deprecated constructs.
   */
  public void setAcceptOld(boolean acceptOld) {
    this.acceptOld = acceptOld;
  }
  

  /**
   * Typechecks an AST.
   * @param ast the AST to check
   * @return the detected errors 
   */
  public List<FbError> process(Declaration ast) {
    boolType = PrimitiveType.mk(PrimitiveType.Ptype.BOOL);
    intType = PrimitiveType.mk(PrimitiveType.Ptype.INT);
    refType = PrimitiveType.mk(PrimitiveType.Ptype.REF);
    nameType = PrimitiveType.mk(PrimitiveType.Ptype.NAME);
    anyType = PrimitiveType.mk(PrimitiveType.Ptype.ANY);
    errType = PrimitiveType.mk(PrimitiveType.Ptype.ERROR);
    
    typeOf = new HashMap<Expr, Type>();
    typeVar = new StackedHashMap<AtomId, Type>();
    enclosingTypeVar = new StackedHashMap<AtomId, AtomId>();
    
    // build symbol table
    SymbolTableBuilder stb = new SymbolTableBuilder();
    errors = stb.process(ast);
    if (!errors.isEmpty()) return errors;
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
    return errors;
  }

  /**
   * Returns the flow graph of {@code impl}.
   * @param impl the implementation whose flow graph is requested
   * @return the flow graph of {@code impl}
   */
  public SimpleGraph<Block> getFlowGraph(Implementation impl) {
    return flowGraphs.getFlowGraph(impl);
  }
  
  /**
   * Returns the map of expressions to types.
   * @return the map of expressions to types.
   */
  public Map<Expr, Type> getTypes() {
    return typeOf;
  }
  
  /**
   * Returns the map from implementations to procedures.
   * @return the map from implementations to procedures
   */
  public UsageToDefMap<Implementation, Procedure> getImplProc() {
    return implProc;
  }
  
  /**
   * Returns the map from implementation parameters to procedure parameters.
   * @return the map from implementation parameters to procedure parameters
   */
  public UsageToDefMap<VariableDecl, VariableDecl> getParamMap() {
    return paramMap;
  }
  
  /**
   * Returns the symbol table.
   * @return the symbol table
   */
  public SymbolTable getST() {
    return st;
  }
  
  // === helper methods ===
  
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
      if (tt.getName().equals(a)) return UserType.mk(b, tt.loc());
      return t;
    } else if (t instanceof ArrayType) {
      ArrayType tt = (ArrayType)t;
      return ArrayType.mk(
        subst(tt.getRowType(), a, b),
        subst(tt.getColType(), a, b),
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
  
  private boolean sub(ArrayType a, ArrayType b) {
    if (!sub(b.getRowType(), a.getRowType())) return false;
    if (a.getColType()==null ^ b.getColType() == null) return false;
    else if (a.getColType() != null)
      if (!sub(b.getColType(), a.getColType())) return false;
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
    if (isTypeVar(a) != isTypeVar(b)) {
      if (isTypeVar(a)) mapTypeVar(a, b);
      else mapTypeVar(b, a);
      return true;
    } else if (isTypeVar(a)) {
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
    else if (a instanceof ArrayType && b instanceof ArrayType)
      return sub((ArrayType)a, (ArrayType)b);
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
            TypeUtils.typeToString(t), t.loc()));
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
    } else if (t instanceof ArrayType) {
      ArrayType at = (ArrayType)t;
      return ArrayType.mk(
          substRealType(at.getRowType()),
          substRealType(at.getColType()),
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

  private void mapTypeVar(Type a, Type b) {
    assert a instanceof UserType;
    AtomId ai = getTypeVarDecl(a);
    Type rt = realType(b);
    if (getTypeVarDecl(rt) != ai)
      typeVar.put(ai, rt);
  }

  private void equalTypeVar(Type a, Type b) {
    // TODO: Randomize
    mapTypeVar(a, b);
  }

  private void mapExplicitGenerics(Identifiers tv, TupleType t) {
    if (t == null) return;
    if (tv == null) {
      errors.add(new FbError(FbError.Type.GEN_TOOMANY, t));
      return;
    }
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
      checkExact(l, r, binaryOp);
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
      typeVar.push();
      mapExplicitGenerics(vd.getTypeVars(), types);
      t = checkRealType(vd.getType(), atomId);
      typeVar.pop();
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
  public PrimitiveType eval(AtomQuant atomQuant, AtomQuant.QuantType quant, Declaration vars, Trigger trig, Expr e) {
    Type t = e.eval(this);
    check(t, boolType, e);
    typeOf.put(atomQuant, boolType);
    return boolType;
  }

  @Override
  public Type eval(AtomFun atomFun, String function, TupleType types, Exprs args) {
    Function d = st.funcs.def(atomFun);
    Signature sig = d.getSig();
    Declaration fargs = sig.getArgs();
    
    typeVar.push();
    mapExplicitGenerics(sig.getTypeVars(), types);
    Type at = strip(args == null? null : (TupleType)args.eval(this));
    Type fat = strip(tupleTypeOfDecl(fargs));
   
    check(at, fat, args == null? atomFun : args);
    Type rt = strip(checkRealType(
          tupleTypeOfDecl(sig.getResults()), atomFun));
    typeVar.pop();
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
  public Type eval(AtomIdx atomIdx, Atom atom, Index idx) {
    Type t = strip(atom.eval(this));
    if (t == errType) return errType;
    if (!(t instanceof ArrayType)) {
      errors.add(new FbError(FbError.Type.NEED_ARRAY, atom));
      return errType;
    }
    ArrayType at = (ArrayType)t;

    // look at indexing types
    typeVar.push();
    check(idx.getA().eval(this), at.getRowType(), idx.getA());
    if (idx.getB() != null)
      check(idx.getB().eval(this), at.getColType(), idx.getB());

    Type et = checkRealType(at.getElemType(), atomIdx);
    typeVar.pop();
    typeOf.put(atomIdx, et);
    return et;
  }
  
  // === visit commands ===
  @Override
  public Type eval(AssignmentCmd assignmentCmd, Expr lhs, Expr rhs) {
    Type lt = strip(lhs.eval(this));
    Type rt = strip(rhs.eval(this));
    check(rt, lt, assignmentCmd);
    return null;
  }

  @Override
  public Type eval(AssertAssumeCmd assertAssumeCmd, AssertAssumeCmd.CmdType type, Expr expr) {
    Type t = expr.eval(this);
    check(t, boolType, assertAssumeCmd);
    return null;
  }

  @Override
  public Type eval(CallCmd callCmd, String procedure, TupleType types, Identifiers results, Exprs args) {
    Procedure p = st.procs.def(callCmd);
    Signature sig = p.getSig();
    Declaration fargs = sig.getArgs();
    
    // check the actual arguments against the formal ones
    Type at = strip(args == null? null : args.eval(this));
    Type fat = strip(tupleTypeOfDecl(fargs));
    check(at, fat, (args == null? callCmd : args));
    
    // check the assignment of the results
    Type lt = strip(results == null? null : results.eval(this));
    Type rt = strip(tupleTypeOfDecl(sig.getResults()));
    check(rt, lt, callCmd);
    
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
  public Type eval(Axiom axiom, Identifiers typeVars, Expr expr, Declaration tail) {
    enclosingTypeVar.push();
    collectEnclosingTypeVars(typeVars);
    Type t = expr.eval(this);
    check(t, boolType, expr);
    enclosingTypeVar.pop();
    if (tail != null) tail.eval(this);
    return null;
  }

  // === keep track of formal generics (see also eval(Axiom...)) ===
  @Override
  public Type eval(Function function, Signature sig, Declaration tail) {
    if (tail != null) tail.eval(this);
    return null;
  }

  @Override
  public Type eval(VariableDecl variableDecl, String name, Type type, Identifiers typeVars, Declaration tail) {
    if (tail != null) tail.eval(this);
    return null;
  }

  @Override
  public Type eval(Procedure procedure, Signature sig, Specification spec, Declaration tail) {
    enclosingTypeVar.push();
    collectEnclosingTypeVars(sig.getTypeVars());
    if (spec != null) spec.eval(this);
    enclosingTypeVar.pop();
    if (tail != null) tail.eval(this);
    return null;
  }

  @Override
  public Type eval(Implementation implementation, Signature sig, Body body, Declaration tail) {
    enclosingTypeVar.push();
    collectEnclosingTypeVars(sig.getTypeVars());
    body.eval(this);
    enclosingTypeVar.pop();
    if (tail != null) tail.eval(this);
    return null;
  }

  // === do not look at block successors ===
  @Override
  public Type eval(Block block, String name, Commands cmds, Identifiers succ, Block tail) {
    if (cmds != null) cmds.eval(this);
    if (tail != null) tail.eval(this);
    return null;
  }
}
