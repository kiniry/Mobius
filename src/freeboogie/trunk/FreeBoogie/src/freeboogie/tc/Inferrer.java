package freeboogie.tc;

import java.util.*;
import java.util.logging.Logger;

import genericutils.Id;

import freeboogie.ast.*;


/**
 * Infers probable types for some of the nodes on which
 * (bottom-up) type-checking failed. The input is an AST and a
 * map of some of its nodes to types. Some nodes may be mapped to
 * the 'error' type. A subset of these are keys in the output:
 * a map from nodes to probable types. The probable types can
 * be 'real' types or type variables ({@code UserType}s with no
 * corresponding declaration).
 *
 * All this class guarantees is that it "tries to do a good job."
 * It is here only to support constructs that are considered
 * deprecated.
 *
 * <b>Implementation.</b> The AST is processed bottom-up. Bad nodes
 * receive as probable type a fresh type variable. Some nodes (such
 * as the binary operators == and &amp;&amp;) impose equality 
 * restrictions between the nodes of the children and/or primitive
 * types. This is implemented with a union-find data structure that
 * keeps as class representant the real (primitive) type, if present.
 *
 * @author rgrig
 */
public class Inferrer extends Transformer {

  private static final Logger log = Logger.getLogger("freeboogie.tc"); 

  // parent.get(x) is a type "equal" to x
  // this never happens: x is a real type and parent.get(x) is a tv
  // the keys represent the introduced type variables
  private Map<UserType, Type> parent;

  // contains the mapping found by the typechecker
  // shall not be modified
  private Map<Expr, Type> typeOf;

  // contains the result, the probable good types for some of the
  // erronuous types
  private Map<Expr, Type> probableTypeOf;

  // used for union-find
  private final Random rand = new Random(123);

  private static final PrimitiveType intType = 
    PrimitiveType.mk(PrimitiveType.Ptype.INT, -1);
  private static final PrimitiveType boolType = 
    PrimitiveType.mk(PrimitiveType.Ptype.BOOL, -1);

  // === public interface ===
  
  /** See the class description. */
  public void process(Declaration ast, Map<Expr, Type> typeOf) {
    this.typeOf = typeOf;
    probableTypeOf = new HashMap<Expr, Type>();
    parent = new HashMap<UserType, Type>();
    ast.eval(this);
  }

  /** 
   * Returns probable types for the nodes that were marked with
   * 'error' types. NOTE: The map may contain as values (i.e.,
   * 'good types') some new {@code UserType}s. The user of this
   * class is responsible for adding proper declarations (such
   * as 'type T' or a generic type as in 'function foo&lt;T&gt;').
   */
  public Map<Expr, Type> getGoodTypes() {
    for (Map.Entry<Expr, Type> e : probableTypeOf.entrySet()) {
      if (!(e.getValue() instanceof UserType)) continue;
      UserType ov = (UserType)e.getValue();
      if (!parent.containsKey(ov)) continue;
      e.setValue(getParent(ov));
    }
    for (Map.Entry<Expr, Type> e : probableTypeOf.entrySet()) {
      log.fine("inferred type " + TypeUtils.typeToString(e.getValue()) +
        " at " + e.getKey().loc());
    }
    return probableTypeOf; 
  }

  // === workers ===
  
  @Override
  public void enterNode(Ast n) {
    if (!(n instanceof Expr)) return;
    Expr e = (Expr)n;
    if (!err(e)) return;
    UserType tv = freshTv();
    probableTypeOf.put(e, tv);
    parent.put(tv, tv);
    log.finer("introduce type variable " + tv.getName() + " at " +
      n.loc());
  }
  
  @Override
  public void see(BinaryOp binaryOp, BinaryOp.Op op, Expr left, Expr right) {
    left.eval(this); right.eval(this);
    Type lt = getType(left);
    Type rt = getType(right);
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
      mkEqual(lt, intType);
      mkEqual(rt, intType);
      break;
    case EQUIV:
    case IMPLIES:
    case AND:
    case OR:
      mkEqual(lt, boolType);
      mkEqual(rt, boolType);
      break;
    case EQ:
    case NEQ:
      mkEqual(lt, rt);
      break;
    case SUBTYPE:
      // don't infer anything
      break;
    default:
      assert false; // unexpected binary operator
    }
  }

  @Override
  public void see(AtomOld atomOld, Expr e) {
    e.eval(this);
    mkEqual(getType(e), getType(atomOld));
  }
  
  // === helpers ===

  private boolean err(Expr e) {
    Type t = typeOf.get(e);
    if (!(t instanceof PrimitiveType)) return false;
    PrimitiveType pt = (PrimitiveType)t;
    return pt.getPtype() == PrimitiveType.Ptype.ERROR;
  }
 
  private UserType freshTv() {
    return UserType.mk(Id.get("tv"), null);
  }

  private void mkEqual(Type a, Type b) {
    if (!isTv(a) && !isTv(b)) return;
    if (isTv(a)) a = getParent((UserType)a);
    if (isTv(b)) b = getParent((UserType)b);
    if (!isTv(a) || isTv(b) && rand.nextBoolean()) {
      Type t = a; a = b; b = t;
    }
    log.finer("type equality: " +
      TypeUtils.typeToString(a) + "==" + TypeUtils.typeToString(b));
    parent.put((UserType)a, b);
  }

  private Type getParent(UserType a) {
    Type b = parent.get(a);
    if (b == a) return a;
    if (isTv(b)) b = getParent((UserType)b);
    parent.put(a, b);
    return b;
  }

  private boolean isTv(Type t) {
    if (!(t instanceof UserType)) return false;
    return parent.containsKey((UserType)t);
  }

  private Type getType(Expr e) {
    if (!err(e)) return typeOf.get(e);
    return probableTypeOf.get(e);
  }
}
