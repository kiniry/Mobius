package mobius.logic.lang.coq.ast;


public abstract class ACleanEvaluator<T> extends AEvaluator<T> {

  @Override
  public final T evalFormula(Formula next) {
    return null;
  }
}
