package mobius.logic.lang.boogie;

//{{{ imports
import freeboogie.ast.DepType;
import freeboogie.ast.Evaluator;
import freeboogie.ast.Expr;
import freeboogie.ast.IndexedType;
import freeboogie.ast.MapType;
import freeboogie.ast.PrimitiveType;
import freeboogie.ast.TupleType;
import freeboogie.ast.Type;
import freeboogie.ast.UserType;
//}}}


/**
 * Builds Generic type names from Boogie types. 
 * @author rgrig@
 */
public class GenericTypeOfBoogie extends Evaluator<String> {
  @Override
  public String eval(DepType depType, Type type, Expr pred) {
    // TODO(rgrig): do something with the predicate?
    return type.eval(this);
  }

  @Override
  public String eval(IndexedType indexedType, Type param, Type type) {
    // TODO(rgrig): handle param?
    return type.eval(this);
  }

  @Override
  public String eval(MapType mapType, TupleType idxType, Type elemType) {
    StringBuilder sb = new StringBuilder();
    sb.append("Map");
    sb.append(idxType.eval(this));
    sb.append(elemType.eval(this));
    return sb.toString();
  }

  @Override
  public String eval(PrimitiveType primitiveType, PrimitiveType.Ptype ptype) {
    switch (ptype) {
      case BOOL: return "Bool";
      case INT: return "Int";
      case REF: return "Ref";
      case NAME: return "Name";
      case ANY: return "Any";
      default:
        assert false;
        return null;
    }
  }

  @Override
  public String eval(TupleType tupleType, Type type, TupleType tail) {
    StringBuilder sb = new StringBuilder();
    sb.append(type.eval(this));
    if (tail != null) { sb.append(tail.eval(this)); }
    return sb.toString();
  }

  @Override
  public String eval(UserType userType, String name) {
    return name;
  }
}
