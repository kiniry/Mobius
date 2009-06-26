package mobius.bmlvcgen.util;


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
  public E peek() {
    return elements[elements.length - 1];
  }

  /** {@inheritDoc} */
  public E pop() {
    final E result = elements[elements.length - 1];
    count = count - 1;
    if (elements.length > 2 * count) {
      shrink();
    }
    return result;
  }

  /** {@inheritDoc} */
  public void push(final E elem) {
    while (count >= elements.length) {
      grow();
    }
    elements[count++] = elem;
  }
  
  /** {@inheritDoc} */
  public boolean isEmpty() {
    return count == 0;
  }
  
  @SuppressWarnings("unchecked")
  private void grow() {
    final int len = 2 * elements.length + 1;
    final E[] newArr = (E[]) new Object[len];
    System.arraycopy(elements, 0, newArr, 0, elements.length);
    elements = newArr;
  }
  
  private void shrink() {
    final int len = 2 * elements.length / 2;
    final E[] newArr = (E[]) new Object[len];
    System.arraycopy(elements, 0, newArr, 0, len);
    elements = newArr;
  }
  
}
