package mobius.logic.lang.boogie;

// {{{ imports
import java.util.Map;
import java.util.Set;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;

import freeboogie.ast.Ast;
import freeboogie.ast.Axiom;
import freeboogie.ast.BinaryOp;
import freeboogie.ast.ConstDecl;
import freeboogie.ast.Declaration;
import freeboogie.ast.Expr;
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
  }

  public Declaration getFrom(final TypeCheckedAst typedGeneric) {
    tc = typedGeneric.getTypeChecker();
    return (Declaration) typedGeneric.eval(this);
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalApplication(final Term next, final Term first) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalAtom(final Term next, final String id) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Declaration evalClauseList(final LinkedList<GenericAst> list) {
    Iterator<GenericAst> it = list.descendingIterator();
    result = null;
    while (it.hasNext()) {
      it.next().eval(this);
    }
    return result;
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalDoc(final String content) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalForall(final Term next, final Atom vars, final Term term) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  // TODO: what to do with generics? (in axioms and global declarations...)
  // TODO: constants vs variables
  @Override
  public Ast evalClause(final String id, final Term term) {
    if (isSpecial(id)) return result;

    GType t = tc.getType(id);
    if (t == null) {
      result = Axiom.mk(null, (Expr) term.eval(this), result);
    } 
    else if (t.getArity() > 1) {
      // translate to function
      Declaration args = getArgs(t);
      Declaration result = VariableDecl.mk(
        Id.get("unnamed"), 
        convertType(t.getReturn()),
        null,
        null); 
      Signature sig = Signature.mk(id, args, result, null);
      result = Function.mk(sig, result);
    } 
    else if (t.isTopType()) {
      result = TypeDecl.mk(id, result);
    }
    else {
      result = ConstDecl.mk(id, convertType(t), false, result);
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

  private Declaration getArgs(GType gt) {
    assert gt != null;
    if (gt.isLast()) return null;
    Type t = convertType(gt);
    Declaration tail = getArgs(gt.getNext());
    return VariableDecl.mk(Id.get("unnamed"), t, null, tail);
  }

  private Type convertType(GType t) {
    PrimitiveType.Ptype ptype = typeFromName.get(t.getName());
    return ptype == null? UserType.mk(t.getName()) : PrimitiveType.mk(ptype);
  }
}
