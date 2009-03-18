package mobius.logic.lang.coq.ast;

import mobius.logic.lang.ast.Ast;
import mobius.logic.lang.coq.ast.Evaluator;

public abstract class CoqAst extends Ast {
  private CoqAst next;
  private CoqAst last;
  
  public CoqAst() {
    next = null;
    last = this;
  }
  
  /**
   * Dispatches to {@code e.eval} based on the static type of the node
   * and the dynamic type of {@code e}.
   * @param <R> the type of the result computed by the evaluator
   * @param e the evaluator
   * @return the result computed by the evaluator
   */
  abstract public <R> R eval(Evaluator<R> e);
  
  public void add(CoqAst next) {
    last.next = next;
    last = next;
  }
  public CoqAst getNext() {
    return next;
  }  

}
