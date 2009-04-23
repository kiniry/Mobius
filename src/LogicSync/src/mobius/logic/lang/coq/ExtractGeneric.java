package mobius.logic.lang.coq;

import java.util.LinkedList;
import java.util.List;

import mobius.logic.lang.coq.ast.ACleanEvaluator;
import mobius.logic.lang.coq.ast.AxiomType;
import mobius.logic.lang.coq.ast.ConstrList;
import mobius.logic.lang.coq.ast.Constructor;
import mobius.logic.lang.coq.ast.CoqAst;
import mobius.logic.lang.coq.ast.Formula;
import mobius.logic.lang.coq.ast.HintType;
import mobius.logic.lang.coq.ast.ReqType;
import mobius.logic.lang.coq.ast.Variable;
import mobius.logic.lang.coq.ast.VariableList;
import mobius.logic.lang.generic.GType;
import mobius.logic.lang.generic.ast.Application;
import mobius.logic.lang.generic.ast.Atom;
import mobius.logic.lang.generic.ast.Clause;
import mobius.logic.lang.generic.ast.ClauseList;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.Term;

public class ExtractGeneric extends ACleanEvaluator<GenericAst> {
  
  public static GenericAst translate(CoqAst ast) {
    CoqAst node = ast;
    final ExtractGeneric trans = new ExtractGeneric();
    final LinkedList<GenericAst> list = new LinkedList<GenericAst>();
    while (node != null) {
      final GenericAst gen = node.eval(trans);
      if (gen != null) {
        list.add(gen);
      }
      node = node.getNext();
    }
    return  ClauseList.mk(list);
  }

  @Override
  public GenericAst evalApplication(final Formula next, 
                                    final Formula first) {
    final Term current = (Term) first.eval(this);
    Term tnext = null;
    if (next != null) {
      tnext = (Term) next.eval(this);
    }
    final Application a = Application.mk(tnext, current);
    return a;
  }

  @Override
  public GenericAst evalBinaryTerm(Formula next, Formula op, Formula left,
                                   Formula right) {
    final Term snd = (Term) left.eval(this);
    snd.setNext((Term)right.eval(this));
    final Term fst = (Term) op.eval(this);
    fst.setNext(snd);
    Term tnext = null;
    if (next != null) {
      tnext = (Term) next.eval(this);
    }
    return Application.mk(tnext, fst);
  }
  
  
  @Override
  public GenericAst evalAxiom(final AxiomType type, 
                              final String name, 
                              final Formula formula) {
    if (type.equals(AxiomType.Variable)) {
      if (formula instanceof mobius.logic.lang.coq.ast.Term) {
        final mobius.logic.lang.coq.ast.Term t = 
          (mobius.logic.lang.coq.ast.Term) formula;
        if (t.getName().equals("Set")) {
          return Clause.mk(name, Atom.mk(null, GType.TopType));
        }
      }
    }
    return evalLemma(name, formula, null);
  }

  /** 
   * Compute the arity for the predicates.
   * @param formula which is an applications
   * @return the number of applications
   */
  private int getDepth(final Formula formula) {
    if (formula instanceof mobius.logic.lang.coq.ast.Application) {
      final mobius.logic.lang.coq.ast.Application app = 
        (mobius.logic.lang.coq.ast.Application) formula;
      return 1 + getDepth(app.getFirst().getNext());
    }
    return 0;
  }

  
  
  @Override
  public GenericAst evalConstrList(Constructor first, Constructor last) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public GenericAst evalConstructor(Constructor next, String name, Formula type) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public GenericAst evalDefinition(String name, Formula type, Formula def,
                                   String proof) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public GenericAst evalDoc(final String content) {
    return mobius.logic.lang.generic.ast.Doc.mk(content.replace('[', '(').replace(']', ')'));
  }

  @Override
  public GenericAst evalExists(Formula next, Variable list, Formula formula) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public GenericAst evalForall(final Formula next, 
                               final VariableList list, 
                               final Formula formula) {
    final mobius.logic.lang.generic.ast.Forall forall = 
      mobius.logic.lang.generic.ast.Forall.mk(null, 
                                              (Atom) list.eval(this), 
                                              (Term) formula.eval(this));
    return forall;
  }



  @Override
  public GenericAst evalFun(Formula next, VariableList list, Formula formula) {
    // TODO Auto-generated method stub
    return null;
  }



  @Override
  public GenericAst evalInductive(String name, Formula type, ConstrList list) {
    // TODO Auto-generated method stub
    return null;
  }

  
  @Override
  public GenericAst evalLemma(final String name, 
                              final Formula formula, 
                              final String proof) {
    final Term t = (Term) formula.eval(this);
    final Clause f = Clause.mk(name, t);
    return f;
  }


  @Override
  public GenericAst evalTerm(final Formula next, final String name) {
    Term t = null;
    if (next != null) {
      t = (Term) next.eval(this);
    }
    return Atom.mk(t, name);
  }

  @Override
  public GenericAst evalVariable(final Variable next, 
                                 final String name, 
                                 final Formula type) {
    Atom n = null;
    if (next != null) {
      n = (Atom) next.eval(this);
    }
    return Atom.mk(n, name);
  }

  @Override
  public GenericAst evalVariableList(final Variable first, 
                                     final Variable tail) {
    return first.eval(this);
  }
  
  
  /** {@inheritDoc} */
  @Override
  public GenericAst evalComment(final String content) {
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public GenericAst evalRequire(final String lib, final ReqType type) {
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public GenericAst evalTactic(final String name, final String namelist,
                               final String content) {
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public GenericAst evalHint(final HintType type, 
                             final List<String> list, 
                             final String lib) {
    return null;
  }
 
  
  /** {@inheritDoc} */
  @Override
  public GenericAst evalOpenScope(final String name) {
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public GenericAst evalCoercion(final String name, 
                                 final String typeFrom, final String typeTo) {
    return null;
  }


}
