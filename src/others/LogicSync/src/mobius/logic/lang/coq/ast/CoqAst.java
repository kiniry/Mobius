package mobius.logic.lang.coq.ast;

import mobius.logic.lang.ast.Ast;
import mobius.logic.lang.coq.ast.Evaluator;

public class CoqAst extends Ast {
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
  public <R> R eval(Evaluator<R> e) {
    return null;
  }
  public void addFirst(CoqAst n) {
    n.next = next;
    next = n;
    if (last == null) {      
      last = next;
    }
  }
  public void add(CoqAst next) {
    if (next != null) {
      last.next = next;
      last = next;
    }
  }
  public CoqAst getNext() {
    return next;
  }

  @Override
  public Ast clone() {
    CoqAst n = new CoqAst();
    n.next = next != null? (CoqAst) next.clone() :  null;
    CoqAst curr = n;
    while (curr.next != null) {
      curr = curr.next;
    }
    n.last = curr;
    return null;
  }  

}
