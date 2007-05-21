/** Public domain. */

package freeboogie.tc;

import java.io.StringWriter;
import java.util.HashMap;

import freeboogie.ast.*;
import freeboogie.ast.utils.PrettyPrinter;
import freeboogie.util.Err;

/**
 * Typechecks an AST. Errors are reported using the class {@code Err}.
 * It maps expressions to types.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
@SuppressWarnings("unused") // many unused parameters
public class TypeChecker extends Evaluator<Type> {
  
  // used for primitive types
  private PrimitiveType boolType, intType, refType, nameType, anyType;
  
  private SymbolTable st;
  
  // where there any type errors?
  private boolean errors;
  
  // TODO: should I make all type ref-comparable here?
  // maps expressions to their types
  private UsageToDefMap<Expr, Type> typeOf;

  // Maps type variables to the real types.
  // Gets set by the |check| functions.
  private HashMap<String, Type> typeVar;
  
  // to get unique names for the type variables
  private int typeVarCnt;
  private static final String TYPE_VAR_PREFIX = " tv";
    // contains space so that it can't come from parsing
  
  // === main entry point(s) ===

  /**
   * Typechecks an AST.
   * @param ast the AST to check
   * @return whether there were any errors while typechecking (or in earlier phases) 
   */
  public boolean process(Declaration ast) {
    boolType = new PrimitiveType(PrimitiveType.Ptype.BOOL);
    intType = new PrimitiveType(PrimitiveType.Ptype.INT);
    refType = new PrimitiveType(PrimitiveType.Ptype.REF);
    nameType = new PrimitiveType(PrimitiveType.Ptype.NAME);
    anyType = new PrimitiveType(PrimitiveType.Ptype.ANY);
    
    typeOf = new UsageToDefMap<Expr, Type>();
    typeVar = new HashMap<String, Type>();
    
    errors = false;
    typeVarCnt = 0;
    SymbolTableBuilder stb = new SymbolTableBuilder();
    boolean nameErrors = stb.process(ast);
    if (!nameErrors) {
      st = stb.getST();
      ast.eval(this);
    }
    return nameErrors || errors;
  }
  
  // === helper methods ===
  
  // TODO: don't forget to check that the where expressions are booleans
  // strip DepType since only the prover can handle the where clauses
  private Type stripDep(Type t) {
    while (t instanceof DepType) t = ((DepType)t).getType();
    return t;
  }
  
  // replaces all occurrences of UserType(a) with UserType(b) 
  private Type subst(Type t, String a, String b) {
    if (t instanceof UserType) {
      UserType tt = (UserType)t;
      if (tt.getName().equals(a)) return new UserType(b, tt.loc());
      return t;
    } else if (t instanceof ArrayType) {
      ArrayType tt = (ArrayType)t;
      return new ArrayType(
        subst(tt.getRowType(), a, b),
        subst(tt.getColType(), a, b),
        subst(tt.getElemType(), a, b),
        tt.loc());
    } else if (t instanceof GenericType) {
      GenericType tt = (GenericType)t;
      return new GenericType(
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
  
  // returns the name of the type variable or null if |t| is not a type variable
  private String typeVarName(Type t) {
    if (t instanceof UserType) {
      UserType s = (UserType)t;
      if (typeVar.containsKey(s.getName()))
        return s.getName();
    }
    return null;
  }
  
  // If |a| is a type variable, then unify it with b.
  // Returns whether a unification was performed.
  private boolean unify(Type a, Type b) {
    String an = typeVarName(a);
    if (an == null) return false;
    
    String bn;
    while ((bn = typeVarName(b)) != null && typeVar.get(bn) != null) 
      b = typeVar.get(bn);
    
    Type c = typeVar.get(an);
    sub(c, b); sub(b, c);
    
    typeVar.put(an, b);
    return true;
  }
  
  // returns (a <: b)
  private boolean sub(Type a, Type b) {
    if (a == b) return true; // the common case
    if (a == null || b == null) return true; // don't trickle up errors
    
    // check if b is ANY
    if (b instanceof PrimitiveType) {
      PrimitiveType sb = (PrimitiveType)b;
      if (sb.getPtype() == PrimitiveType.Ptype.ANY) return true;
    }
    
    // the `generics' hack
    if (unify(a, b) || unify(b, a)) return true;
    
    // allow T to be used when <tv>T is needed and tv is a type variable
    if (b instanceof GenericType && !(a instanceof GenericType)) {
      GenericType sb = (GenericType)b;
      if (typeVarName(sb.getParam()) != null && sub(a, sb.getType()))
        return unify(sb.getParam(), anyType);
    }
    
    // the main check
    if (a instanceof PrimitiveType) {
      if (!(b instanceof PrimitiveType)) return false;
      PrimitiveType sa = (PrimitiveType)a;
      PrimitiveType sb = (PrimitiveType)b;
      return sa.getPtype() == sb.getPtype();
    } else if (a instanceof ArrayType) {
      if (!(b instanceof ArrayType)) return false;
      ArrayType sa = (ArrayType)a;
      ArrayType sb = (ArrayType)b;
      if (!sub(sb.getRowType(), sa.getRowType())) return false;
      if ((sa.getColType()==null) != (sb.getColType()==null)) return false;
      else if (sa.getColType() != null)
        if (!sub(sb.getColType(), sa.getColType())) return false;
      return sub(sa.getElemType(), sb.getElemType());
    } else if (a instanceof UserType) {
      if (!(b instanceof UserType)) return false;
      UserType sa = (UserType)a;
      UserType sb = (UserType)b;
      return sa.getName().equals(sb.getName()); // TODO: is names OK here?
    } else if (a instanceof GenericType) {
      if (!(b instanceof GenericType)) return false;
      GenericType sa = (GenericType)a;
      GenericType sb = (GenericType)b;
      if (!sub(sa.getParam(), sb.getParam()) || !sub(sb.getParam(), sa.getParam()))
        return false;
      return sub(sa.getType(), sb.getType());
    } else {
      Err.help("type = " + a);
      assert false;
    }
      
    return false;
  }
  
  // pretty print a type
  private String typeToString(Type t) {
    StringWriter sw = new StringWriter();
    PrettyPrinter pp = new PrettyPrinter(sw);
    t.eval(pp);
    return sw.toString();
  }
  
  /**
   * If {@code a} cannot be used where {@code b} is expected then an error
   * at location {@code l} is produced and {@code errors} is set.
   */
  private void check(Type a, Type b, AstLocation l) {
    if (sub(a, b)) return;
    Err.error("" + l + ": Used type " + typeToString(a) 
      + " when expecting " + typeToString(b) + ".");
    errors = true;
  }
  
  /**
   * Same as {@code check}, except it is more picky about the types:
   * They must be exactly the same.
   */
  private void checkExact(Type a, Type b, AstLocation l) {
    if (sub(a, b) && sub(b, a)) return;
    Err.error("" + l + ": Types should be the same: " 
      + typeToString(a) + " and " + typeToString(b) + ".");
    errors = true;
  }
  
  // === visiting operators ===
  @Override
  public Type eval(UnaryOp unaryOp, UnaryOp.Op op, Expr e) {
    Type t = stripDep(e.eval(this));
    switch (op) {
    case MINUS:
      check(t, intType, e.loc());
      typeOf.put(unaryOp, intType);
      return intType;
    case NOT:
      check(t, boolType, e.loc());
      typeOf.put(unaryOp, boolType);
      return boolType;
    default:
      assert false;
      return null; // dumb compiler
    }
  }

  @Override
  public Type eval(BinaryOp binaryOp, BinaryOp.Op op, Expr left, Expr right) {
    Type l = stripDep(left.eval(this));
    Type r = stripDep(left.eval(this));
    switch (op) {
    case PLUS:
    case MINUS:
    case MUL:
    case DIV:
    case MOD:
      // integer arguments and integer result
      check(l, intType, left.loc());
      check(r, intType, right.loc());
      typeOf.put(binaryOp, intType);
      return intType;
    case LT:
    case LE:
    case GE:
    case GT:
      // integer arguments and boolean result
      check(l, intType, left.loc());
      check(r, intType, right.loc());
      typeOf.put(binaryOp, boolType);
      return boolType;
    case EQUIV:
    case IMPLIES:
    case AND:
    case OR:
      // boolean arguments and boolean result
      check(l, boolType, left.loc());
      check(r, boolType, right.loc());
      typeOf.put(binaryOp, boolType);
      return boolType;
    case SUBTYPE:
      // l subtype of r and boolean result (TODO: a user type is a subtype of a user type)
      check(l, r, left.loc());
      typeOf.put(binaryOp, boolType);
      return boolType;
    case EQ:
    case NEQ:
      // typeOf(l) == typeOf(r) and boolean result
      checkExact(l, r, binaryOp.loc());
      typeOf.put(binaryOp, boolType);
      return boolType;
    default:
      assert false;
      return null; // dumb compiler
    }
  }
  
  // === visiting atoms, including arrays with that `generic' hack ===
  @Override
  public Type eval(AtomId atomId, String id) {
    Declaration d = st.ids.def(atomId);
    Type t = null;
    if (d == null)
      // HACK for `generics'
      t = new UserType(id, null);
    else {
      if (d instanceof VariableDecl)
        t = ((VariableDecl)d).getType();
      else if (d instanceof ConstDecl)
        t = ((ConstDecl)d).getType();
      else
        assert false;
    }
    typeOf.put(atomId, t);
    return t;
  }

  @Override
  public Type eval(AtomFun atomFun, String function, Exprs args) {
    Function d = st.funcs.def(atomFun);
    Signature sig = d.getSig();
    // TODO: I must have a list of types as a type!
    assert false; // TODO: Implement.
    return null;
  }


  @Override
  public Type eval(AtomCast atomCast, Expr e, Type type) {
    // TODO: should I make some casts fail?
    e.eval(this);
    return type;
  }

  @Override
  public Type eval(AtomIdx atomIdx, Atom atom, Index idx) {
    Type t = stripDep(atom.eval(this));
    if (t == null) return null; // don't repeat error messages
    if (!(t instanceof ArrayType)) {
      Err.error("" + atom.loc() + ": Must be an array.");
      errors = true;
      return null;
    }
    ArrayType at = (ArrayType)t;
    Type et = at.getElemType();

    // the bulk of the `generic' hack
    String resultTypeVar = null;
    String freshTypeVar = null;
    if (et instanceof UserType) {
      UserType uet = (UserType)et;
      if (st.types.def(uet) == null) {
        // make uet a type variable
        resultTypeVar = uet.getName();
        freshTypeVar = TYPE_VAR_PREFIX + typeVarCnt++;
        at = (ArrayType)subst(at, resultTypeVar, freshTypeVar);
        typeVar.put(freshTypeVar, null);
      }
    }
    
    // look at indexing types
    check(stripDep(idx.getA().eval(this)), stripDep(at.getRowType()), idx.getA().loc());
    if (idx.getB() != null)
      check(stripDep(idx.getB().eval(this)), stripDep(at.getColType()), idx.getB().loc());

    // get the result type in case it was a type variable
    if (resultTypeVar != null) {
      et = typeVar.get(freshTypeVar);
      typeVar.remove(freshTypeVar);
    }
    
    
    // TODO: report error when et == null? seems right but the benchmarks
    // are full of these errors.
    //if (et == null) {
    //  Err.error("" + atomIdx.loc() + ": Unable to deduce type of array element.");
    //  errors = true;
    //}
    
    typeOf.put(atomIdx, et);
    return et;
  }

  
  // === visiting functions ===

}
