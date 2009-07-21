package freeboogie.tc;

import java.io.PrintWriter;
import java.io.StringWriter;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import genericutils.Err;

/**
 * Various utilities for handling {@code Type}. For the moment, it contains
 * a structural equality test that ignores AST locations. 
 *
 * @author rgrig 
 */
public final class TypeUtils {
  private TypeUtils() { /* forbid instantiation */ }
  
  // TODO: reuse this code for TypeChecker.sub. how?
  
  private static boolean eq(MapType a, MapType b) {
    return
      eq(a.getElemType(), b.getElemType()) &&
      eq(a.getIdxType(), b.getIdxType());
  }
  
  private static boolean eq(PrimitiveType a, PrimitiveType b) {
    return a.getPtype() == b.getPtype();
  }
  
  private static boolean eq(IndexedType a, IndexedType b) {
    return eq(a.getParam(), b.getParam()) && eq(a.getType(), b.getType());
  }
  
  private static boolean eq(UserType a, UserType b) {
    return a.getName().equals(b.getName());
  }
  
  private static boolean eq(TupleType a, TupleType b) {
    if (a == b) return true;
    if (a == null ^ b == null) return false;
    return eq(a.getType(), b.getType()) && eq(a.getTail(), b.getTail());
  }

  /**
   * Recursively strip all dependent types from {@code a}.
   * @param a the type to strip of predicates
   * @return the type {@code a} striped of predicates
   */
  public static Type stripDep(Type a) {
    if (a instanceof MapType) {
      MapType sa = (MapType)a;
      return MapType.mk(
        (TupleType)stripDep(sa.getIdxType()), 
        stripDep(sa.getElemType()));
    } else if (a instanceof IndexedType) {
      IndexedType sa = (IndexedType)a;
      return IndexedType.mk(stripDep(sa.getParam()), stripDep(sa.getType()));
    } else if (a instanceof TupleType) {
      TupleType sa = (TupleType)a;
      return TupleType.mk(stripDep(sa.getType()), (TupleType)stripDep(sa.getTail()));
    } else if (a instanceof DepType) return stripDep(((DepType)a).getType());
    else return a;
  }
  
  private static Declaration stripDep(Declaration a) {
    if (!(a instanceof VariableDecl)) return a;
    VariableDecl va = (VariableDecl)a;
    return VariableDecl.mk(
        null,
        va.getName(), 
        stripDep(va.getType()),
        va.getTypeArgs(),
        stripDep(va.getTail()), 
        va.loc());
  }

  /**
   * Returns a signature that looks like {@code s} but has all predicates
   * of dependent types removed.
   * @param s the signature to strip
   * @return the signature {@code s} without dependent types
   */
  public static Signature stripDep(Signature s) {
    return Signature.mk(
        s.getName(),
        s.getTypeArgs(),
        stripDep(s.getArgs()), 
        stripDep(s.getResults()),
        s.loc());
  }
  
  /**
   * Compares two types for structural equality, ignoring locations
   * and predicates of dependent types.
   * @param a the first type
   * @param b the second type
   * @return whether the two types are structurally equal
   */
  public static boolean eq(Type a, Type b) {
    if (a == b) return true;
    if (a == null ^ b == null) return false;
    if (a instanceof MapType && b instanceof MapType)
      return eq((MapType)a, (MapType)b);
    else if (a instanceof PrimitiveType && b instanceof PrimitiveType)
      return eq((PrimitiveType)a, (PrimitiveType)b);
    else if (a instanceof IndexedType && b instanceof IndexedType)
      return eq((IndexedType)a, (IndexedType)b);
    else if (a instanceof UserType && b instanceof UserType)
      return eq((UserType)a, (UserType)b);
    else if (a instanceof TupleType && b instanceof TupleType)
      return eq((TupleType)a, (TupleType)b);
    else
      return false;
  }

  /**
   * Returns whether {@code t} contains a dependent type.
   * @param t the type to check
   * @return whether {@code t} contains {@code DepType}
   */
  public static boolean hasDep(Type t) {
    if (t instanceof DepType) return true;
    else if (t instanceof MapType) {
      MapType st = (MapType)t;
      return 
        hasDep(st.getElemType()) || 
        hasDep(st.getIdxType());
    } else if (t instanceof IndexedType) {
      IndexedType st = (IndexedType)t;
      return hasDep(st.getParam()) || hasDep(st.getType());
    } else if (t instanceof TupleType) {
      TupleType st = (TupleType)t;
      return hasDep(st.getType()) || hasDep(st.getTail());
    }
    return false;
  }

  /**
   * Pretty print a type.
   * @param t the type to pretty print
   * @return the string representation of {@code t}
   */
  public static String typeToString(Type t) {
    if (t == null) return "()";
    StringWriter sw = new StringWriter();
    PrettyPrinter pp = new PrettyPrinter(sw);
    t.eval(pp);
    if (t instanceof TupleType)
      return "(" + sw + ")";
    else 
      return sw.toString();
  }
  
  public static boolean isInt(Type t) {
    return isPrimitive(t, PrimitiveType.Ptype.INT);
  }

  public static boolean isBool(Type t) {
    return isPrimitive(t, PrimitiveType.Ptype.BOOL);
  }

  public static boolean isPrimitive(Type t, PrimitiveType.Ptype p) {
    if (!(t instanceof PrimitiveType)) return false;
    PrimitiveType pt = (PrimitiveType)t;
    return pt.getPtype() == p;
  }

  public static boolean isTypeVar(Type t) {
    assert false : "todo";
    return false;
  }

  /**
   * Typechecks {@code ast} using {@code tc}. Raises an internal
   * error if the typecheck fails.
   */
  public static Declaration internalTypecheck(Declaration ast, TcInterface tc) {
    if (!tc.process(ast).isEmpty()) {
      PrintWriter pw = new PrintWriter(System.out);
      PrettyPrinter pp = new PrettyPrinter(pw);
      ast.eval(pp);
      pw.flush();
      Err.internal("Invalid Boogie produced.");
    }
    return tc.getAST();
  }
}
