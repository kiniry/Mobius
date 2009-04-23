package mobius.logic.lang.nat;

import java.util.LinkedList;
import java.util.List;

import mobius.logic.lang.generic.GType;
import mobius.logic.lang.generic.ast.Atom;
import mobius.logic.lang.generic.ast.Clause;
import mobius.logic.lang.generic.ast.ClauseList;
import mobius.logic.lang.generic.ast.Doc;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.nat.ast.AEvaluator;
import mobius.logic.lang.nat.ast.Item;
import mobius.logic.lang.nat.ast.Logic;

public class NLToGenericTranslator extends AEvaluator<GenericAst> {

  private String logicName;
  
  private LinkedList<GenericAst> clauses;
  
  public NLToGenericTranslator() {
    
  }
  
  @Override
  public GenericAst evalItem(final String id, final String description) {
    clauses.add(Doc.mk(description));
    clauses.add(Clause.mk(id, Atom.mk(null, GType.TopType)));
    return null;
  }

  @Override
  public GenericAst evalLogic(final String name, final List<Item> items) {
    logicName = name;    
    for (Item item : items) {
      item.eval(this);
    }
    return null;
  }

  @Override
  public GenericAst evalProgram(final List<Logic> logics) {
    clauses = new LinkedList<GenericAst>();
    for (Logic logic : logics) {
      logic.eval(this);
    }
    return ClauseList.mk(clauses);
  }

}
