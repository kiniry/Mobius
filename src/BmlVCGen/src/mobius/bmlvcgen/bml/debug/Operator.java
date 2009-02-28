package mobius.bmlvcgen.bml.debug;

/**
 * Information about an operator, used for printing expressions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface Operator {
  /** Possible associativities. */
  enum Assoc {
    /** Left. */
    LEFT, 
    /** Right. */
    RIGHT, 
    /** Both. */
    BOTH,
    /** Not associative. */
    NOASSOC;
  }
  
  /**
   * Get string representation of this operator.
   * @return Operator as string.
   */
  String getText();
  
  /** 
   * Get associativity of this operator. 
   * @return Associativity.
   */
  Assoc getAssoc();
  
  /**
   * Get operator priority.
   * @return Operator priority.
   */
  int getPriority();
}
