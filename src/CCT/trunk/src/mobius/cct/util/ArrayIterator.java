package mobius.cct.util;

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * Iterator for arrays. Remove operation is not supported.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <T> Type of objects stored in the array.
 */
public class ArrayIterator<T> implements Iterator<T> {
  /**
   * Array.
   */
  private final T[] fArray;
  
  /**
   * Current index.
   */
  private int fCurrent;
  
  /**
   * Stop iteration before reaching this index.
   */
  private final int fBound;
  
  /**
   * Constructor.
   * @param array Array.
   */
  public ArrayIterator(final T[] array) {
    if (array == null) {
      throw new IllegalArgumentException("array == null");
    }
    fArray = array;
    fCurrent = 0;
    fBound = array.length;
  }

  /**
   * Constructor. Iterate starting from given index.
   * @param array Array.
   * @param start First index used.
   */
  public ArrayIterator(final T[] array, final int start) {
    if (array == null) {
      throw new IllegalArgumentException("array == null");
    }
    if (start < 0) { 
      throw new IllegalArgumentException("start < 0"); 
    }
    fArray = array;
    fCurrent = start;
    fBound = array.length;
  }

  /**
   * Constructor. Iterate over objects with indices
   * in range start..bound-1.
   * @param array Array.
   * @param start First index used.
   * @param bound First index that is NOT used.
   */
  public ArrayIterator(final T[] array, 
                       final int start, final int bound) {
    if (array == null) {
      throw new IllegalArgumentException("array == null");
    }
    if (start < 0) { 
      throw new IllegalArgumentException("start < 0"); 
    }
    fArray = array;
    fCurrent = start;
    if (bound < array.length) {
      fBound = bound;
    } else {
      fBound = array.length;
    }
  }
  
  /**
   * hasNext().
   * @return .
   */
  public boolean hasNext() {
    return fCurrent < fBound;
  }

  /**
   * next().
   * @return .
   */
  public T next() {
    if (fCurrent < fBound) {
      return fArray[fCurrent++];
    } else {
      throw new NoSuchElementException();
    }
  }

  /**
   * Element removal is not supported.
   */
  public void remove() {
    throw new UnsupportedOperationException();
  }

}
