package mobius.cct.util;

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * Empty iterator.
 * @param <E> Type of elements.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class EmptyIterator<E> implements Iterator<E> {
  /**
   * Return false.
   * @return false.
   */
  public boolean hasNext() {
    return false;
  }

  /**
   * Throw NoSuchElementException.
   * @return Throws an exception.
   */
  public E next() {
    throw new NoSuchElementException();
  }

  /**
   * Throws IllegalStateException.
   */
  public void remove() {
    throw new IllegalStateException();
  }

}
