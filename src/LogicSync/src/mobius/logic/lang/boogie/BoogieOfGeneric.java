package mobius.logic.lang.boogie;

// {{{ imports
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import freeboogie.ast.Ast;
import freeboogie.ast.AtomCast;
import freeboogie.ast.AtomFun;
import freeboogie.ast.AtomId;
import freeboogie.ast.AtomQuant;
import freeboogie.ast.AtomLit;
import freeboogie.ast.Axiom;
import freeboogie.ast.BinaryOp;
import freeboogie.ast.ConstDecl;
import freeboogie.ast.Declaration;
import freeboogie.ast.Expr;
import freeboogie.ast.Exprs;
import freeboogie.ast.Function;
import freeboogie.ast.PrimitiveType;
import freeboogie.ast.Signature;
import freeboogie.ast.Type;
import freeboogie.ast.TypeDecl;
import freeboogie.ast.UnaryOp;
import freeboogie.ast.UserType;
import freeboogie.ast.VariableDecl;
import freeboogie.util.Id;
import mobius.logic.lang.generic.GType;
import mobius.logic.lang.generic.TypeChecker;
import mobius.logic.lang.generic.ast.ACleanEvaluator;
import mobius.logic.lang.generic.ast.Atom;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.Term;
import mobius.logic.lang.generic.ast.TypeCheckedAst;

// }}}

/**
 * Constructs a Boogie AST while visiting a generic one.
 * @author rgrig@
 */
public class BoogieOfGeneric extends ACleanEvaluator<Ast> {
  /** 
   * Maps special ids in the generic language to the corresponding
   * Boogie binary operator.
   */
  private static Map<String, BinaryOp.Op> binaryOpFromName;

  /** 
   * Maps special ids in the generic language to the corresponding
   * Boogie unary operator.
   */
  private static Map<String, UnaryOp.Op> unaryOpFromName;

  /**
   * Maps special ids in the generic language to the corresponding
   * Boogie primitive types.
   */
  private static Map<String, PrimitiveType.Ptype> typeFromName;

  /** 
   * These are not translated to Boogie at all, usually because 
   * they are implicit there.
   */
  private static Set<String> ignoredIds;

  /** These ids are translated into casts. */
  private static Set<String> castIds;

  private static Pattern castPattern = Pattern.compile("(.*)_to_(.*)");

  /** Typechecker for the generic language. */
  private TypeChecker tc;

  /** Accumulates the Boogie AST being built. */
  private Declaration result;

  static {
    binaryOpFromName = new HashMap<String, BinaryOp.Op>();
    unaryOpFromName = new HashMap<String, UnaryOp.Op>();
    typeFromName = new HashMap<String, PrimitiveType.Ptype>();
    ignoredIds = new HashSet<String>();
    castIds = new HashSet<String>();

    unaryOpFromName.put("negb", UnaryOp.Op.NOT);
    unaryOpFromName.put("not", UnaryOp.Op.NOT);
    
    binaryOpFromName.put("integralLE", BinaryOp.Op.LE);
    binaryOpFromName.put("Zeq_bool", BinaryOp.Op.EQ);
    binaryOpFromName.put("Seq", BinaryOp.Op.EQ);
    binaryOpFromName.put("=", BinaryOp.Op.EQ);
    binaryOpFromName.put("\\/", BinaryOp.Op.OR);
    binaryOpFromName.put("bor", BinaryOp.Op.OR);
    binaryOpFromName.put("->", BinaryOp.Op.IMPLIES);

    castIds.add("S_to_Z");
    castIds.add("Z_to_S");
    castIds.add("S_to_bool");

    typeFromName.put("Z", PrimitiveType.Ptype.INT);
    typeFromName.put("Prop", PrimitiveType.Ptype.BOOL);
    typeFromName.put("bool", PrimitiveType.Ptype.BOOL);

    ignoredIds.add("Z_to_S_elim");
    ignoredIds.add("T");
  }

  public Declaration getFrom(final TypeCheckedAst typedGeneric) {
    tc = typedGeneric.getTypeChecker();
    return (Declaration) typedGeneric.eval(this);
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalApplication(final Term next, final Term first) {
    String op = ((Atom) first).getId();
    UnaryOp.Op unaryOp;
    BinaryOp.Op binaryOp;
    if ((unaryOp = unaryOpFromName.get(op)) != null) {
      return UnaryOp.mk(unaryOp, (Expr) first.getNext().eval(this));
    }
    else if ((binaryOp = binaryOpFromName.get(op)) != null) {
      return BinaryOp.mk(
        binaryOp, 
        (Expr) first.getNext().eval(this),
        (Expr) first.getNext().getNext().eval(this));
    }
    else if (castIds.contains(op)) {
      return AtomCast.mk(
        (Expr) first.getNext().eval(this), 
        getHackishName(op));
    }
    else return AtomFun.mk(
      op, 
      null, 
      getActualArgs(first.getNext()));
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalAtom(final Term next, String id) {
    // TODO: true/false
    if (id.equals("true") || id.equals("True")) {
      return AtomLit.mk(AtomLit.AtomType.TRUE);
    }
    else if (id.equals("false") || id.equals("False")) {
      return AtomLit.mk(AtomLit.AtomType.FALSE);
    }
    else if (id.equals("null")) id = "Null";
    return AtomId.mk(id, null);
  }

  /** {@inheritDoc} */
  @Override
  public Declaration evalClauseList(final LinkedList<GenericAst> list) {
    Iterator<GenericAst> it = list.descendingIterator();
System.out.println("  reset result");
    result = null;
    while (it.hasNext()) {
      it.next().eval(this);
    }
    return result;
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalDoc(final String content) {
    return null; // TODO(rgrig): put comment in FreeBoogie AST
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalForall(final Term next, final Atom vars, final Term term) {
    return wrapInForall((Expr) term.eval(this), vars);
  }

  /** {@inheritDoc} */
  // TODO: what to do with generics? (in axioms and global declarations...)
  // TODO: constants vs variables
  @Override
  public Ast evalClause(String id, final Term term) {
    if (isSpecial(id)) return result;

System.out.println("  process " + id);
    GType t = tc.getType(id);
    if (t == null) {
      result = Axiom.mk(id, null, (Expr) term.eval(this), result);
    } 
    else if (t.getArity() > 1) {
      // translate to function
      Declaration args = getArgs(t);
      Declaration funResult = VariableDecl.mk(
        Id.get("unnamed"), 
        convertType(t.getReturn().getName()),
        null,
        null); 
      Signature sig = Signature.mk(id, args, funResult, null);
      result = Function.mk(sig, result);
    } 
    else if (t.isTopType()) {
      result = TypeDecl.mk(id, result);
    }
    else {
      if (id.equals("null")) id = "Null";
      result = ConstDecl.mk(id, convertType(t.getName()), false, result);
      // TODO: when to make variables?
    }
    return result;
  }

  private boolean isSpecial(final String id) {
    return
      binaryOpFromName.containsKey(id) ||
      unaryOpFromName.containsKey(id) ||
      typeFromName.containsKey(id) ||
      castIds.contains(id) ||
      ignoredIds.contains(id);
  }

  private Declaration getArgs(final GType gt) {
    assert gt != null;
    if (gt.isLast()) return null;
    Type t = convertType(gt.getName());
    Declaration tail = getArgs(gt.getNext());
    return VariableDecl.mk(Id.get("unnamed"), t, null, tail);
  }

  private Exprs getActualArgs(final Term term) {
    if (term == null) return null;
    return Exprs.mk((Expr) term.eval(this), getActualArgs(term.getNext()));
  }

  private Expr wrapInForall(final Expr e, final Atom vars) {
    if (vars == null) return e;
    return AtomQuant.mk(
      AtomQuant.QuantType.FORALL,
      VariableDecl.mk(
        vars.getId(),
        convertType(tc.getTermType(vars).getName()),
        null,
        null),
      null,
      wrapInForall(e, (Atom) vars.getNext()));
  }

  private Type convertType(String t) {
    PrimitiveType.Ptype ptype = typeFromName.get(t);
    return ptype == null? UserType.mk(t) : PrimitiveType.mk(ptype);
  }

  private Type getHackishName(String castId) {
    Matcher m = castPattern.matcher(castId);
    if (!m.matches()) {
      throw new IllegalStateException("wrong stuff in castIds");
    }
    assert m.groupCount() == 2;
    return convertType(m.group(2));
  }
}
