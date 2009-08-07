package freeboogie.vcgen;

import java.util.HashSet;
import java.util.logging.Logger;

import freeboogie.ast.*;
import freeboogie.tc.TcInterface;
import freeboogie.tc.TypeUtils;

/**
 * Replaces all map reads and writes by explicit calls to
 * <tt>select</tt> and <tt>update</tt>.
 */
public class MapRemover extends Transformer {
  private static final Logger log = Logger.getLogger("freeboogie.vcgen");
  private HashSet<Integer> arities = new HashSet<Integer>(7);

  @Override
  public Declaration process(Declaration ast, TcInterface tc) {
    arities.clear();
    ast = (Declaration)ast.eval(this);
    for (Integer n : arities) {
      // add "function $$selectN<TV, T1, ..., TN>
      //        (map : [T1, ..., TN]TV, x1 : T1, ..., xN : TN)
      //        returns (result : TV);"
      ast = FunctionDecl.mk(
        null,
        Signature.mk(
          "$$select" + n,
          Identifiers.mk(AtomId.mk("TV", null), nIdentifiers("T", n)),
          VariableDecl.mk(
            null,
            "map",
            MapType.mk(
              nTypes(n),
              UserType.mk("TV", null)
            ),
            null,
            nVarDecl("x", n, null)),
          VariableDecl.mk(
            null,
            "result",
            UserType.mk("TV", null),
            null,
            null)),
        ast);

      // add "function $$updateN<TV, T1, ..., TN>
      //        (val : TV, map : [T1, ..., TN]TV, x1 : T1, ..., xN : TN)
      //        returns (result : [T1, ..., TN]TV);"
      ast = FunctionDecl.mk(
        null,
        Signature.mk(
          "$$update" + n,
          Identifiers.mk(AtomId.mk("TV", null), nIdentifiers("T", n)),
          VariableDecl.mk(
            null,
            "val",
            UserType.mk("TV", null),
            null,
            VariableDecl.mk(
              null,
              "map",
              MapType.mk(
                nTypes(n),
                UserType.mk("TV", null)),
              null,
            nVarDecl("x", n, null))),
          VariableDecl.mk(
            null,
            "result",
            MapType.mk(
              nTypes(n),
              UserType.mk("TV", null)),
            null,
            null)),
        ast);

      // add "axiom<TV, T1, ..., TN>
      //        (forall m : [T1, ..., TN]TV, v : TV, x1 : T1, ..., xN : TN ::
      //          $$selectN($$updateN(v, m, x1, ..., xN), x1, ..., xN) == v
      //        );
      Expr axiomExpr;
      axiomExpr = BinaryOp.mk(
        BinaryOp.Op.EQ,
        AtomId.mk("v", null),
        AtomFun.mk(
          "$$select" + n,
          null,
          Exprs.mk(
            AtomFun.mk(
              "$$update" + n,
              null,
              Exprs.mk(AtomId.mk("v", null),
              Exprs.mk(AtomId.mk("m", null),
              nExprs("x", n)))),
            nExprs("x", n))));
      axiomExpr = AtomQuant.mk(
        AtomQuant.QuantType.FORALL,
        VariableDecl.mk(
          null,
          "m",
          MapType.mk(nTypes(n), UserType.mk("TV", null)),
          null,
        VariableDecl.mk(
          null,
          "v",
          UserType.mk("TV", null),
          null,
        nVarDecl("x", n, null))),
        null, 
        axiomExpr);
      ast = Axiom.mk(
        null,
        "select_update_" + n,
        Identifiers.mk(AtomId.mk("TV", null), nIdentifiers("T", n)),
        axiomExpr,
        ast);

      for (int i = n; i > 0; --i) {
        // "axiom<TV, T1, ..., TN>
        //    (forall m : [T1, ..., TN] TV, v : TV,
        //      x1 : T1, ..., xN : TN, y1 : T1, ..., yN : TN ::
        //      xi != yi ==>
        //      $$selectN($$updateN(v, m, x1, ..., xN), y1, ..., yN) ==
        //        $$selectN(m, y1, ..., yN));
        axiomExpr = BinaryOp.mk(
          BinaryOp.Op.IMPLIES,
          BinaryOp.mk(
            BinaryOp.Op.NEQ,
            AtomId.mk("x" + i, null),
            AtomId.mk("y" + i, null)),
          BinaryOp.mk(
            BinaryOp.Op.EQ,
            AtomFun.mk(
              "$$select" + n,
              null,
              Exprs.mk(
                AtomFun.mk(
                  "$$update" + n,
                  null,
                  Exprs.mk(AtomId.mk("v", null),
                  Exprs.mk(AtomId.mk("m", null),
                  nExprs("x", n)))),
                nExprs("y", n))),
            AtomFun.mk(
              "$$select" + n,
              null,
              Exprs.mk(AtomId.mk("m", null),
              nExprs("y", n)))));
        axiomExpr = AtomQuant.mk(
          AtomQuant.QuantType.FORALL,
          VariableDecl.mk(
            null,
            "m",
            MapType.mk(nTypes(n), UserType.mk("TV", null)),
            null,
          VariableDecl.mk(
            null,
            "v",
            UserType.mk("TV", null),
            null,
          nVarDecl("x", n,
          nVarDecl("y", n, null)))),
          null,
          axiomExpr);
        ast = Axiom.mk(
          null,
          "select_update_diff_" + n,
          Identifiers.mk(AtomId.mk("TV", null), nIdentifiers("T", n)),
          axiomExpr,
          ast);
      } // for i
    } // for arities

    return TypeUtils.internalTypecheck(ast, tc);
  }

  @Override
  public AtomFun eval(AtomMapSelect atomMapSelect, Atom atom, Exprs idx) {
    atom = (Atom)atom.eval(this);
    idx = (Exprs)idx.eval(this);
    int n = size(idx);
    arities.add(n);
    return AtomFun.mk("$$select" + n, null, Exprs.mk(atom, idx));
  }

  @Override
  public AtomFun eval(AtomMapUpdate atomMapUpdate, Atom atom, Exprs idx, Expr val) {
    atom = (Atom)atom.eval(this);
    idx = (Exprs)idx.eval(this);
    val = (Expr)val.eval(this);
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

  // returns "p1, ..., pN"
  private Identifiers nIdentifiers(String prefix, int n) {
    Identifiers result;
    for (result = null; n > 0; --n)
      result = Identifiers.mk(AtomId.mk(prefix + n, null), result);
    return result;
  }

  // returns "p1, ..., pN"
  private Exprs nExprs(String prefix, int n) {
    Exprs result;
    for (result = null; n > 0; --n)
      result = Exprs.mk(AtomId.mk(prefix + n, null), result);
    return result;
  }

  // return "T1, ..., TN"
  private TupleType nTypes(int n) {
    TupleType result;
    for (result = null; n > 0; --n)
      result = TupleType.mk(UserType.mk("T" + n, null), result);
    return result;
  }

  // returns "x1 : T1, ...., xN : TN, tail"
  private VariableDecl nVarDecl(String prefix, int n, VariableDecl tail) {
    for (; n > 0; --n) {
      tail = VariableDecl.mk(
        null,
        prefix + n,
        UserType.mk("T" + n, null),
        null,
        tail);
    }
    return tail;
  }
}
