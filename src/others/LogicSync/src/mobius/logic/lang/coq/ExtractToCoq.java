package mobius.logic.lang.coq;

import java.util.LinkedList;

import mobius.logic.lang.coq.ast.Application;
import mobius.logic.lang.coq.ast.Axiom;
import mobius.logic.lang.coq.ast.AxiomType;
import mobius.logic.lang.coq.ast.BinaryTerm;
import mobius.logic.lang.coq.ast.CoqAst;
import mobius.logic.lang.coq.ast.Doc;
import mobius.logic.lang.coq.ast.Forall;
import mobius.logic.lang.coq.ast.Formula;
import mobius.logic.lang.coq.ast.ReqType;
import mobius.logic.lang.coq.ast.Require;
import mobius.logic.lang.coq.ast.Variable;
import mobius.logic.lang.coq.ast.VariableList;
import mobius.logic.lang.generic.ast.ACleanEvaluator;
import mobius.logic.lang.generic.ast.Atom;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.Term;

public class ExtractToCoq extends ACleanEvaluator<CoqAst> {

  /** 
   * @param next ignored
   * @param id the name of the term
   * @return a Term with the name corresponding to the id. 
   */
  @Override
  public CoqAst evalAtom(final Term next, final String id) {
    return mkCTerm(id);
  }

  @Override
  public CoqAst evalClauseList(final LinkedList<GenericAst> list) {
    final CoqAst ast = new CoqAst();
    for (GenericAst mem: list) {
      ast.add(mem.eval(this));
    }
    return ast;
  }

  @Override
  public CoqAst evalDoc(final String content) {
    return Doc.mk(content);
  }


  
  
  @Override
  public CoqAst evalClause(final String id, final Term term) {
    return mkVariable(id, (Formula) term.eval(this));
  }


  private static CoqAst mkVariable(final String id, final Formula type) {
    return Axiom.mk(AxiomType.Variable, id, type); 
  }
  
  private static mobius.logic.lang.coq.ast.Term mkCTerm(final String id) {
    return mobius.logic.lang.coq.ast.Term.mk(null, id); 
  }


  /**
   * Extract a Coq AST out of a generic AST.
   * @param ast the generic AST to extract from
   * @return the generated AST
   */
  public static CoqAst extract(final GenericAst ast) {
    final ExtractToCoq e = new ExtractToCoq();
    final CoqAst cast = ast.eval(e);
    cast.addFirst(Require.mk("ZArith", ReqType.Import));
    return cast;
  }

  @Override
  public CoqAst evalForall(final Term next, final Atom vars, final Term term) {
    final Variable first = Variable.mk(null, vars.getId(), null);
    Variable tail = first;
    Atom curr = vars;
    while (curr.getNext() != null) {
      curr = (Atom) curr.getNext();
      tail.setNext(Variable.mk(null, curr.getId(), null));
      tail = tail.getNext();
    }
    final VariableList vlist = VariableList.mk(first, tail);
    return Forall.mk(null, vlist, (Formula) term.eval(this));
  }
  
  @Override
  public CoqAst evalApplication(final Term next, final Term first) {
    final Formula f = evalApplicationMembers(first);
    if (f instanceof mobius.logic.lang.coq.ast.Term) {
      final mobius.logic.lang.coq.ast.Term t = 
        (mobius.logic.lang.coq.ast.Term) f;
      if (isBinarySymbol(t.getName())) {
        return BinaryTerm.mk(null, t, t.getNext(), t.getNext().getNext());
      }
    }
    return Application.mk(null, f);
  }

  private static boolean isBinarySymbol(final String name) {
    return name.equals("->") || 
           name.equals("<>") ||
           name.equals("=");
  }

  private Formula evalApplicationMembers(final Term first) {
    Term t = first.getNext();
    final Formula res = (Formula) first.eval(this);
    Formula f = res;
    while (t != null) {
      f.setNext((Formula)t.eval(this));
      f = f.getNext();
      t = t.getNext();
    }
    return res;
  }
 
}
