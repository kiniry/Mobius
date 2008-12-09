package freeboogie.vcgen;

import java.io.PrintWriter;
import java.util.HashSet;
import java.util.List;
import java.util.logging.Logger;

import freeboogie.ast.*;
import freeboogie.astutil.PrettyPrinter;
import freeboogie.tc.FbError;
import freeboogie.tc.TcInterface;
import freeboogie.util.Err;

/**
 * Replaces all map reads and writes by explicit calls to
 * <tt>select</tt> and <tt>update</tt>.
 */
public class MapRemover extends Transformer {
  private static final Logger log = Logger.getLogger("freeboogie.vcgen");
  private HashSet<Integer> arities = new HashSet<Integer>(7);

  public Declaration process(Declaration ast, TcInterface tc) {
    arities.clear();
    ast = (Declaration)ast.eval(this);
    for (Integer n : arities) {
      // add "function $$selectN<TV, T1, ..., TN>
      //        (map : [T1, ..., TN]TV, x1 : T1, ..., xN : TN)
      //        returns (result : TV);"
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
          Identifiers.mk(AtomId.mk("TV", null), nIdentifiers("T", n))),
        ast);
      // add "function $$updateN<TV, T1, ..., TN>
      //        (val : TV, map : [T1, ..., TN]TV, x1 : T1, ..., xN : TN)
      //        returns (result : [T1, ..., TN]TV);"
      ast = Function.mk(
        Signature.mk(
          "$$update" + n,
          VariableDecl.mk(
            "val",
            UserType.mk("TV"),
            null,
            VariableDecl.mk(
              "map",
              MapType.mk(
                nTypes(n),
                UserType.mk("TV")),
              null,
            nVarDecl(n))),
          VariableDecl.mk(
            "result",
            MapType.mk(
              nTypes(n),
              UserType.mk("TV")),
            null,
            null),
          Identifiers.mk(AtomId.mk("TV", null), nIdentifiers("T", n))),
        ast);
      // add "axiom<TV, T1, ..., TN>
      //        (forall m : [T1, ..., TN]TV, v : TV, x1 : T1, ..., xN : TN ::
      //          select(update(v, m, x1, ..., xN), x1, ..., xN) == v
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
          "m",
          MapType.mk(nTypes(n), UserType.mk("TV")),
          null,
        VariableDecl.mk(
          "v",
          UserType.mk("TV"),
          null,
        nVarDecl(n))),
        null, // TODO
        axiomExpr);
      ast = Axiom.mk(
        Identifiers.mk(AtomId.mk("TV", null), nIdentifiers("T", n)),
        axiomExpr,
        ast);
    }

    log.info("Start to typecheck after map removing.");
    List<FbError> errors = tc.process(ast);
    if (!errors.isEmpty()) {
      FbError.reportAll(errors);
      PrintWriter pw = new PrintWriter(System.out);
      PrettyPrinter pp = new PrettyPrinter(pw);
      ast.eval(pp);
      pw.flush();
      Err.fatal("INTERNAL ERROR: MapRemover produced invalid Boogie.");
    }
    return tc.getAST();
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
