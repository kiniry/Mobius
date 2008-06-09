package freeboogie.tc;

import java.util.HashMap;
import java.util.Map;
import freeboogie.ast.*;

/**
 * Given an AST, it infers types for the lowest nodes that were
 * given an errType by the typechecker. This is based on applying
 * top-down heuristics (e.g., if the AST contains a==b then
 * this gets translated into the type equation typeof(a)==typeof(b)).
 *
 * TODO Modify this to include type variables and do equalities on them.
 */
class Inferrer extends Transformer {

  // contains the mapping found by the typechecker
  // shall not be modified
  private Map<Expr, Type> typeOf;

  // contains the result, the probable good types for some of the
  // erronuous types
  private Map<Expr, Type> probableTypeOf;

  private static final PrimitiveType intType = 
    PrimitiveType.mk(PrimitiveType.Ptype.INT);
  private static final PrimitiveType boolType = 
    PrimitiveType.mk(PrimitiveType.Ptype.BOOL);

  // === public interface ===
  
  public void process(Declaration ast, Map<Expr, Type> typeOf) {
    this.typeOf = typeOf;
    probableTypeOf = new HashMap<Expr, Type>();
    ast.eval(this);
  }

  public Map<Expr, Type> getGoodTypes() { return probableTypeOf; }
  
  // === workers ===
  @Override
  public void see(BinaryOp binaryOp, BinaryOp.Op op, Expr left, Expr right) {
    left.eval(this); right.eval(this);
    if (!err(left) && !err(right)) return;
    switch (op) {
    case PLUS:
    case MINUS:
    case MUL:
    case DIV:
    case MOD:
    case LT:
    case GT:
    case LE:
    case GE:
      // left and right must be integers
      if (err(left)) probableTypeOf.put(left, intType);
      if (err(right)) probableTypeOf.put(right, intType);
      break;
    case EQUIV:
    case IMPLIES:
    case AND:
    case OR:
      // left and right must be booleans
      if (err(left)) probableTypeOf.put(left, boolType);
      if (err(right)) probableTypeOf.put(right, boolType);
      break;
    case EQ:
    case NEQ:
      // left and right must have the same type
      if (err(left) && !err(right)) 
        probableTypeOf.put(left, typeOf.get(right));
      if (!err(left) && err(right))
        probableTypeOf.put(right, typeOf.get(left));
      break;
    case SUBTYPE:
      // don't infer anything
      break;
    default:
      assert false; // unexpected binary operator
    }
  }

  // === helpers ===

  private boolean err(Expr e) {
    Type t = typeOf.get(e);
    if (!(t instanceof PrimitiveType)) return false;
    PrimitiveType pt = (PrimitiveType)t;
    return pt.getPtype() == PrimitiveType.Ptype.ERROR;
  }
  
}
