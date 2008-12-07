package freeboogie.vcgen;

import java.util.HashSet;

import freeboogie.ast.*;

/**
 * Replaces all map reads and writes by explicit calls to
 * <tt>select</tt> and <tt>update</tt>.
 */
public class MapRemover extends Transformer {
  private HashSet<Integer> arities = new HashSet<Integer>(7);

  public Declaration process(Declaration ast) {
    arities.clear();
    ast = (Declaration)ast.eval(this);
    for (Integer n : arities) {
      ast = Function.mk(
        Signature.mk(
          "$$select" + n,
          VariableDecl.mk(
            "map",
            MapType.mk(
              nTypes(n),
              UserType.mk("TV")
            ),
            null,
            nVarDecl(n)),
          VariableDecl.mk(
            "result",
            UserType.mk("TV"),
            null,
            null),
          Identifiers.mk(AtomId.mk("TV", null), nIdentifiers(n))),
        ast);
      // TODO add definition for update
      // TODO add axiom
    }
    return ast;
  }

  @Override
  public AtomFun eval(AtomMapSelect atomMapSelect, Atom atom, Exprs idx) {
    int n = size(idx);
    arities.add(n);
    return AtomFun.mk("$$select" + n, null, Exprs.mk(atom, idx));
  }

  @Override
  public AtomFun eval(AtomMapUpdate atomMapUpdate, Atom atom, Exprs idx, Expr val) {
    int n = size(idx);
    arities.add(n);
    return AtomFun.mk(
      "$$update" + n,
      null,
      Exprs.mk(val, Exprs.mk(atom, idx)));
  }

  private int size(Exprs exprs) {
    if (exprs == null) return 0;
    return 1 + size(exprs.getTail());
  }

  // returns "T1, ..., TN"
  private Identifiers nIdentifiers(int n) {
    Identifiers result;
    for (result = null; n > 0; --n)
      result = Identifiers.mk(AtomId.mk("T" + n, null), result);
    return result;
  }

  // return "T1, ..., TN"
  private TupleType nTypes(int n) {
    TupleType result;
    for (result = null; n > 0; --n)
      result = TupleType.mk(UserType.mk("T" + n), result);
    return result;
  }

  // returns "x1 : T1, ...., xN, TN"
  private VariableDecl nVarDecl(int n) {
    VariableDecl result;
    for (result = null; n > 0; --n)
      result = VariableDecl.mk("x" + n, UserType.mk("T" + n), null, result);
    return result;
  }
}
