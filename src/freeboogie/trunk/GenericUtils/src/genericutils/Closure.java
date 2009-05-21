package genericutils;

/**
 * Has the abstract method {@code go}. To be used as a closure.
 *
 * @author rgrig 
 * @param <T> the type of the parameter of {@code go}
 */
public abstract class Closure<T> {
  /**
   * Process {@code t}.
   * @param t what to process
   */
  public abstract void go(T t);
}
