package mobius.bmlvcgen.util;

/**
 * Interface of objects which can be visited.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <Visitor> Type of visitors.
 */
public interface Visitable<Visitor> {
  /**
   * Visit this object.
   * @param visitor Visitor.
   */
  void accept(Visitor visitor);
}
