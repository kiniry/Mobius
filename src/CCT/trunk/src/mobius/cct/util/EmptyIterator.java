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
  @Override
  public boolean hasNext() {
    return false;
  }

  /**
   * Throw NoSuchElementException.
   */
  @Override
  public E next() {
    throw new NoSuchElementException();
  }

  /**
   * Throws IllegalStateException.
   */
  @Override
  public void remove() {
    throw new IllegalStateException();
  }

}
