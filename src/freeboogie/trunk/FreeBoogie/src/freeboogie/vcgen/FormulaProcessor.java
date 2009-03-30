package freeboogie.vcgen;

import java.util.List;

import freeboogie.backend.Term;
import freeboogie.backend.TermBuilder;

/**
 * TODO: description
 *
 * @author Fintan 
 * @author reviewed by TODO
 * @param <T>
 */
public interface FormulaProcessor<T extends Term<T>> {

  /**
   * @param termBuilder
   */
  void setBuilder(TermBuilder<T> termBuilder);
  
  /**
   * @param t
   * @return a
   */
  T process(T t);
  
  /**
   * @param dag 
   * @return a
   */
  List<T> getAxioms(T dag);
  
}
