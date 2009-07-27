package mobius.cct.util;

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * Transforms an iterator over iterators to single iterator. 
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <T> Type of values.
 */
public class FlattenIterator<T> implements Iterator<T> {
  /**
   * Source iterator.
   */
  private final Iterator<? extends Iterator<? extends T>> fSource;

  /**
   * Current iterator.
   */
  private Iterator<? extends T> fCurrent;
  
  /**
   * Iterator from which last element was taken.
   */
  private Iterator<? extends T> fLast;
  
  /**
   * Constructor.
   * @param source Source iterator.
   */
  public FlattenIterator(final Iterator<? extends 
      Iterator<? extends T>> source) {
    fSource = source;
    fCurrent = null; 
    fLast = null;
  }
  
  /**
   * Advance fCurrent to next nonempty iterator.
   * If there are no more nonempty iterators, fCurrent is set
   * to null.
   */
  public void findNext() {
    if ((fCurrent == null) || (!fCurrent.hasNext())) {
      while (fSource.hasNext()) {
        fCurrent = fSource.next();
        if (fCurrent.hasNext()) {
          return;
        }
      }
      fCurrent = null;
    }
  }
  
  /**
   * Return true if there is at least one more element in this iterator.
   * @return True if the iterator has more elements.
   */
  public boolean hasNext() {
    findNext();
    return fCurrent != null;
  }

  /**
   * Return next element.
   * @return Next element.
   */
  public T next() {
    findNext();
    if (fCurrent == null) {
      throw new NoSuchElementException();
    } else {
      fLast = fCurrent;
      return fCurrent.next();
    }
  }

  /**
   * Delegated to iterator from which current element was taken.
   */
  public void remove() {
    if (fLast == null) {
      throw new IllegalStateException();
    } else {
      fLast.remove();
    }
  }
}
