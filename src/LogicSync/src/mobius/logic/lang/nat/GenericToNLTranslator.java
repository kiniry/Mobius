package mobius.logic.lang.nat;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import mobius.logic.lang.generic.ast.AEvaluator;
import mobius.logic.lang.generic.ast.Atom;
import mobius.logic.lang.generic.ast.ClauseList;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.Term;
import mobius.logic.lang.nat.ast.Item;
import mobius.logic.lang.nat.ast.Logic;
import mobius.logic.lang.nat.ast.NLAst;
import mobius.logic.lang.nat.ast.Program;

public class GenericToNLTranslator extends AEvaluator<NLAst> {
  
  private boolean lastClauseWasADoc;
  private String lastDoc;
  private List<Item> items;
  
  private static final String DEFAULT_LOGIC_NAME = "default";
  
  public GenericToNLTranslator() {}
  
  @Override
  public NLAst evalApplication(Term next, Term first) {
    return null;
  }

  @Override
  public NLAst evalAtom(Term next, String id) {
    return null;
  }

  @Override
  public NLAst evalClauseList(LinkedList<GenericAst> list) {
    
    List<Logic> logics = new ArrayList<Logic>(1);
    items = new LinkedList<Item>();
    Logic logic = Logic.mk(DEFAULT_LOGIC_NAME, items);
    logics.add(logic);
    
    for (GenericAst node : list) {
      node.eval(this);
    }
    
    return Program.mk(logics);
  }

  @Override
  public NLAst evalDoc(String content) {
    lastDoc = content;
    lastClauseWasADoc = true;
    return null;
  }

  @Override
  public NLAst evalForall(Term next, Atom vars, Term term) {
    return null;
  }

  @Override
  public NLAst evalClause(String id, Term term) {
    if (lastClauseWasADoc) {
      items.add(Item.mk(id, lastDoc));
    }
    lastClauseWasADoc = false;
    return null;
  }

  @Override
  public NLAst evalTerm(Term next) {
    return null;
  }

  public NLAst translate(GenericAst ast) {
    if (ast instanceof ClauseList) {
      ClauseList list = (ClauseList)ast;
      return this.evalClauseList(list.getList());
    } else {
      return null;
    }
  }
  
}
