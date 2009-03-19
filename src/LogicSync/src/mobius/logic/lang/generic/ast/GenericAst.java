package mobius.logic.lang.generic.ast;

import mobius.logic.lang.ast.Ast;

public abstract class GenericAst extends Ast {
  private GenericAst next;
  private GenericAst last;
  
  public GenericAst() {
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
  
  public void add(GenericAst next) {
    last.next = next;
    last = next;
  }
  public GenericAst getNext() {
    return next;
  }  

}
