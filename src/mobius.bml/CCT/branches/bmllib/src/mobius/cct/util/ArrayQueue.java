package mobius.cct.util;

import java.util.Collection;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Queue;

/**
 * Queue implemented as array. This implementation is not thread-safe.
 * @param <T> Type of elements.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class ArrayQueue<T> implements Queue<T> {
  /**
   * Counter incremented after each modification of the array.
   */
  private long fTime;
  
  /**
   * Array of elements.
   */
  private T[] fElements;
  
  /**
   * Number of elements in queue.
   */
  private int fLength;
  
  /**
   * Queue head (index of first element).
   */
  private int fHead;
  
  /**
   * Queue tail (first index AFTER last element).
   */
  private int fTail;
  
  /**
   * Queue iterator.
   * @author Tadeusz Sznuk (ts209501@gmail.com)
   */
  private final class QueueIterator implements Iterator<T> {
    /**
     * Index of current element in the queue.
     */
    private int fCurrent;

    /**
     * State of the counter when the iterator was created.
     */
    private long fCreationTime;
    
    /**
     * Constructor.
     */
    public QueueIterator() {
      fCreationTime = fTime;
      fCurrent = 0;
    }
    
    /**
     * Check if there are any more elements to be returned by this iterator.
     * @return true iff there is at least one more element to be returned.
     */
    public boolean hasNext() {
      if (fTime != fCreationTime) {
        throw new ConcurrentModificationException();
      }
      return fCurrent < fLength;
    }

    /**
     * Fetch next element.
     * @return Next element.
     */
    public T next() {
      if (fTime != fCreationTime) {
        throw new ConcurrentModificationException();
      }
      if (fCurrent < fLength) {
        final T result = fElements[(fHead + fCurrent) % fElements.length];
        fCurrent++;
        return result;
      } else {
        throw new NoSuchElementException();
      }
    }

    /**
     * Remove current element.
     */
    public void remove() {
      if (fTime != fCreationTime) {
        throw new ConcurrentModificationException();
      }
      if (fCurrent < fLength) {
        removeElement(fCurrent);
        fCreationTime = fTime;
      } else {
        throw new NoSuchElementException();
      }
    }
    
  }
  
  /**
   * Constructor. Creates empty queue.
   */
  @SuppressWarnings("unchecked")
  public ArrayQueue() {
    fTime = 0;
    fElements = (T[])new Object[0];
    fLength = 0;
    fHead = 0;
    fTail = 0;
  }
  
  /**
   * Ensure that the array is large enough to store 
   * requested number of elements.
   * @param size Requested size.
   */
  @SuppressWarnings("unchecked")
  private void grow(final int size) {
    T[] newElements;
    int newSize;
    
    if (size > fElements.length) {
      fTime++;
      newSize = fElements.length;
      while (newSize < size) {
        newSize = 2 * newSize + 1;
      }
      newElements = (T[]) new Object[newSize];
      for (int i = 0; i < fLength; i++) {
        newElements[i] = fElements[(fHead + i) % fElements.length];
      }
      fElements = newElements;
      fHead = 0;
      fTail = fLength;
    }
  }
  
  /**
   * Ensure that the array is at most two times as large as it needs to be
   * to hold all elements of the queue.
   */
  @SuppressWarnings("unchecked")
  private void shrink() {
    T[] newElements;
    int newSize;

    newSize = fElements.length;
    while (newSize > fLength) {
      newSize =  newSize / 2;
    }
    if (newSize != fElements.length) {
      fTime++;
      newElements = (T[]) new Object[newSize];
      for (int i = 0; i < fLength; i++) {
        newElements[i] = fElements[(fHead + i) % fElements.length];
      }
      fElements = newElements;
      fHead = 0;
      fTail = fLength;
    }
  }
  
  /**
   * Remove element with given index in the queue.
   * Queue head has index 0.
   * @param i Element index.
   */
  private void removeElement(final int i) {
    fLength--;
    for (int j = i; j < fLength; j++) {
      fElements[(fHead + j) % fElements.length] = 
        fElements[(fHead + j + 1) % fElements.length];
    }
    shrink();
    fTime++;
  }
  
  /**
   * Add element at the end of queue.
   * @param e Element to be added.
   * @return true.
   */
  public boolean add(final T e) {
    if (e == null) {
      throw new NullPointerException();
    }
    grow(fLength + 1);
    fElements[fTail] = e;
    fTail = (fTail + 1) % fElements.length;
    fTime++;
    fLength++;
    return true;
  }

  /**
   * Retrieve first element of queue. If the queue is empty,
   * {@link NoSuchElementException} is thrown.
   * Returned element is not removed from the queue.
   * @return Queue head.
   */
  public T element() {
    if (fLength > 0) {
      return fElements[fHead];
    } else {
      throw new NoSuchElementException();
    }
  }
  
  /**
   * Add element at the end of queue.
   * @param e Element to be added.
   * @return true.
   */
  public boolean offer(final T e) {
    add(e);
    return true;
  }

  /**
   * Retrieve first element of queue. If the queue is empty,
   * null is returned. Returned element is not removed from the queue.
   * @return Queue head or null.
   */
  public T peek() {
    if (fLength > 0) {
      return fElements[fHead];
    } else {
      return null;
    }
  }

  /**
   * Retrieve and remove head of the queue.
   * If the queue is empty, null is returned.
   * @return Queue head or null.
   */
  public T poll() {
    if (fLength > 0) {
      final T result = fElements[fHead];
      fHead = (fHead + 1) % fElements.length;
      fLength--;
      shrink();
      return result;
    } else {
      return null;
    }
  }

  /**
   * Retrieve and remove head of the queue.
   * If the queue is empty, {@link NoSuchElementException} is thrown.
   * @return Queue head.
   */
  public T remove() {
    if (fLength > 0) {
      final T result = fElements[fHead];
      fHead = (fHead + 1) % fElements.length;
      fTime++;
      return result;
    } else {
      throw new NoSuchElementException();
    }
  }

  /**
   * Add all elements of a collection to the queue.
   * @param c Collection.
   * @return true.
   */
  public boolean addAll(final Collection<? extends T> c) {
    if (c == null) { throw new NullPointerException(); }
    final Iterator<? extends T> i = c.iterator();
    while (i.hasNext()) {
      add(i.next());
    }
    return true;
  }

  /**
   * Remove all elements from queue.
   */
  @SuppressWarnings("unchecked")
  public void clear() {
    fElements = (T[])new Object[0];
    fLength = 0;
    fHead = 0;
    fTail = 0;
  }

  /**
   * Search for given element in queue.
   * @param o Requested object.
   * @return true iff the queue contains requested element.
   */
  public boolean contains(final Object o) {
    if (o == null) { return false; }
    for (int i = 0; i < fLength; i++) {
      if (o.equals(fElements[(fHead + i) % fElements.length])) {
        return true;
      }
    }
    return false;
  }

  /**
   * Search for given collection of elements in queue.
   * @param c Collection to search for.
   * @return true iff the queue contains all elements in collection.
   */
  public boolean containsAll(final Collection<?> c) {
    if (c == null) { throw new NullPointerException(); }
    final Iterator<?> i = c.iterator();
    while (i.hasNext()) {
      if (contains(i.next())) {
        return true;
      }
    }
    return false;
  }

  /**
   * Check if the queue is empty.
   * @return true iff the queue is empty.
   */
  public boolean isEmpty() {
    return fLength == 0;
  }

  /**
   * Iterate over elements in queue (starting from head).
   * @return Iterator.
   */
  public Iterator<T> iterator() {
    return new QueueIterator();
  }

  /**
   * Remove first (starting from head) occurrence of given element
   * from the queue.
   * @param o Element to be removed.
   * @return true iff the element was in the queue.
   */
  public boolean remove(final Object o) {
    if (o == null) { return false; }
    for (int i = 0; i < fLength; i++) {
      if (o.equals(fElements[(fHead + i) % fElements.length])) {
        removeElement(i);
        return true;
      }
    }
    return false;
  }

  /**
   * Remove all occurrences of objects contained in given collection from the queue.
   * @param c Collection of elements to be removed.
   * @return true iff the queue was changed.
   */
  public boolean removeAll(final Collection<?> c) {
    boolean result = false;
    
    if (c == null) { throw new NullPointerException(); }
    for (int i = 0; i < fLength; i++) {
      if (c.contains(fElements[(fHead + i) % fElements.length])) {
        removeElement(i);
        fTime++;
        result = true;
      }
    }
    return result;
  }

  /**
   * Remove all occurrences of objects NOT contained in given collection from the queue.
   * @param c Collection of elements to be retained.
   * @return true iff the queue was changed.
   */
  public boolean retainAll(final Collection<?> c) {
    boolean result = false;
    
    if (c == null) { throw new NullPointerException(); }
    for (int i = 0; i < fLength; i++) {
      if (!c.contains(fElements[(fHead + i) % fElements.length])) {
        fLength--;
        for (int j = i; j < fLength; j++) {
          fElements[(fHead + j) % fElements.length] = 
            fElements[(fHead + j + 1) % fElements.length];
        }
        shrink();
        fTime++;
        result = true;
      }
    }
    return result;
  }

  /**
   * Return number of elements in queue.
   * @return Size.
   */
  public int size() {
    return fLength;
  }

  /**
   * Convert queue to array. Modifications of the returned array
   * do affect the queue in any way.
   * @return Array with queue elements.
   */
  public Object[] toArray() {
    final Object[] result = new Object[fLength];
    for (int i = 0; i < fLength; i++) {
      result[i] = fElements[(fHead + i) % fElements.length];
    }
    return result;
  }

  /**
   * Convert queue to array. Modifications of the returned array
   * do affect the queue in any way. If the array supplied as argument
   * is large enough to hold all elements of the queue, it is 
   * returned (if it is too large, null elements are added at the end).
   * @param <X> Type of array elements.
   * @param a Array used to determine result type.
   * @return Array with queue elements.
   */
  @SuppressWarnings("unchecked")
  public <X> X[] toArray(final X[] a) {
    if (a.getClass().getComponentType()
        .isAssignableFrom(fElements.getClass().getComponentType())) {
      if (a.length >= fLength) {
        for (int i = 0; i < fLength; i++) {
          a[i] = (X) fElements[(fHead + i) % fElements.length];
        }
        for (int i = fLength; i < a.length; i++) {
          a[i] = null;
        }
        return a;
      } else {
        return (X[]) toArray();
      }
    } else {
      throw new ArrayStoreException();
    }
  }

}
