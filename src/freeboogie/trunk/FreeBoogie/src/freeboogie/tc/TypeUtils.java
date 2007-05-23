/** Public domain. */

package freeboogie.tc;

import java.io.StringWriter;

import freeboogie.ast.*;
import freeboogie.ast.utils.PrettyPrinter;

/**
 * Various utilities for handling {@code Type}. For the moment, it contains
 * a structural equality test that ignores AST locations. 
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class TypeUtils {
  
  // TODO: reuse this code for TypeChecker.sub. how?
  
  private static boolean eq(ArrayType a, ArrayType b) {
    return
      eq(a.getElemType(), b.getElemType()) &&
      eq(a.getRowType(), b.getRowType()) &&
      eq(a.getColType(), b.getColType());
  }
  
  private static boolean eq(PrimitiveType a, PrimitiveType b) {
    return a.getPtype() == b.getPtype();
  }
  
  private static boolean eq(GenericType a, GenericType b) {
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
  
  private static Type strip(Type a) {
    if (a instanceof DepType) return strip(((DepType)a).getType());
    return a;
  }
  
  /**
   * Compares two types for structural equality, ignoring locations
   * and predicates of dependent types.
   * @param a the first type
   * @param b the second type
   * @return whether the two types are structurally equal
   */
  public static boolean eq(Type a, Type b) {
    a = strip(a); b = strip(b);
    if (a == b) return true;
    if (a == null ^ b == null) return false;
    if (a instanceof ArrayType && b instanceof ArrayType)
      return eq((ArrayType)a, (ArrayType)b);
    else if (a instanceof PrimitiveType && b instanceof PrimitiveType)
      return eq((PrimitiveType)a, (PrimitiveType)b);
    else if (a instanceof GenericType && b instanceof GenericType)
      return eq((GenericType)a, (GenericType)b);
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
    else if (t instanceof ArrayType) {
      ArrayType st = (ArrayType)t;
      return 
        hasDep(st.getElemType()) || 
        hasDep(st.getRowType()) || 
        hasDep(st.getRowType()); 
    } else if (t instanceof GenericType) {
      GenericType st = (GenericType)t;
      return hasDep(st.getParam()) || hasDep(st.getType());
    } else if (t instanceof TupleType) {
      TupleType st = (TupleType)t;
      return hasDep(st.getType()) || hasDep(st.getTail());
    }
    return false;
  }

  /**
   * Pretty print a type
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
  
}
