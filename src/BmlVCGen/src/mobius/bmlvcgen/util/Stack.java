package mobius.bmlvcgen.util;

/**
 * Interface of stacks.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <E> Type of elements.
 */
public interface Stack<E> {
  /**
   * Get element from the top of this stack.
   * @return Top element.
   */
  E peek();
  
  /**
   * Remove top element from this stack.
   * @return Remove element.
   */
  E pop();
  
  /**
   * Add element to this stack.
   * @param elem Element to be added.
   */
  void push(E elem);
  
  /**
   * Is this stack empty?
   * @return True iff this stack is empty.
   */
  boolean isEmpty();
}
