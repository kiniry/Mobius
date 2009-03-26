package mobius.logic.lang.generic.ast;


public abstract class ACleanEvaluator<T> extends AEvaluator<T> {

  @Override
  public final T evalTerm(Term next) {
    return null;
  }

}
