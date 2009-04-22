package mobius.logic.lang.boogie;

import java.util.Map;
import java.util.Set;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

import freeboogie.ast.Ast;
import freeboogie.ast.BinaryOp;
import freeboogie.ast.PrimitiveType;
import freeboogie.ast.UnaryOp;
import mobius.logic.lang.generic.ast.ACleanEvaluator;
import mobius.logic.lang.generic.ast.Atom;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.Term;

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

  static {
    binaryOpFromName = new HashMap<String, BinaryOp.Op>();
    unaryOpFromName = new HashMap<String, UnaryOp.Op>();
    typeFromName = new HashMap<String, PrimitiveType.Ptype>();
    ignoredIds = new HashSet<String>();
    castIds = new HashSet<String>();
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
  public Ast evalClauseList(final LinkedList<GenericAst> list) {
    assert false : "not implemented";
    return null;
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
  @Override
  public Ast evalFormula(final String id, final Term term) {
    // if special, don't process
    // ask typechecker if it's a function
      // translate to function
      // translate to axiom
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalSymbol(final String id) {
    assert false : "not implemented";
    return null;
  }
}
