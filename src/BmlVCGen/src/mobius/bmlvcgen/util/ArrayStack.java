package mobius.bmlvcgen.util;

import java.util.Arrays;

/**
 * A simple stack implementation.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 * @param <E> Type of elements.
 */
public final class ArrayStack<E> implements Stack<E> {
  // Elements are kept in an array.
  private E[] elements;
  // Stack size.
  private int count;
  
  /**
   * Constructor - creates empty stack.
   */
  @SuppressWarnings("unchecked")
  public ArrayStack() {
    elements = (E[])new Object[0];
    count = 0;
  }

  /** {@inheritDoc} */  
  @Override
  public E peek() {
    return elements[elements.length - 1];
  }

  /** {@inheritDoc} */
  @Override
  public E pop() {
    final E result = elements[elements.length - 1];
    count = count - 1;
    if (elements.length > 2 * count) {
      shrink();
    }
    return result;
  }

  /** {@inheritDoc} */
  @Override
  public void push(final E elem) {
    while (count >= elements.length) {
      grow();
    }
    elements[count++] = elem;
  }
  
  /** {@inheritDoc} */
  @Override
  public boolean isEmpty() {
    return count == 0;
  }
  
  private void grow() {
    elements = Arrays.copyOf(elements, 2 * elements.length + 1);
  }
  
  private void shrink() {
    elements = Arrays.copyOf(elements, elements.length / 2);
  }
  
}
