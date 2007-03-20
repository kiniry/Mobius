/** Public domain. */

package freeboogie.ast.gen;

import java.io.IOException;

/**
 * Provides a convenient interface for reading a stream of {@code T}s.
 * 
 * Elements are read one by one using the method {@code next}. The current
 * position in the stream can be {@code mark}ed. The method {@code rewind}
 * goes to the closest previous marked position or to the beginning of
 * the stream. The elements from the beginning of the stream to the current
 * position can be {@code eat}en. In general, elements should be eaten
 * whenever you know you will not need to rewind and read them again,
 * so that memory is not wasted.
 *
 * The user of this class should implement the method {@code read}
 * which returns element in order or {@code null} if the end-of-file
 * is reached.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 * @param <T> the type of the stream elements
 */
public abstract class PeekStream<T> {
  /*
   * TODO describe the implementation.
   */

  private class Node<S> {
    /** data */  public S data;
    /** next */ public Node<S> next;
    
    /**
     * {@code next} is set to {@code null}.
     * @param data the data to put in the node
     */
    public Node(S data) {
      this.data = data;
      this.next = null;
    }
    
    /**
     * @param data the data to put in the note
     * @param next the next node
     */
    public Node(S data, Node<S> next) {
      this.data = data;
      this.next = next;
    }
  }
  
  private class ElLocPair {
    /** Element */
    public T elem;
    
    /** Location of _previous_ element. */
    public Location<T> loc;
    
    /**
     * Initialization
     * @param elem the element
     * @param loc the location of the previous element
     */
    public ElLocPair(T elem, Location<T> loc) {
      this.elem = elem; this.loc = loc;
    }
  }
  
  private Node<ElLocPair> buffer;
  private Node<ElLocPair> nextElement; 
  private Node<Node<ElLocPair>> markedStack;
  
  private Location<T> initLoc;

  /**
   * Creates a {@code PeekStream} and sets a location tracking object.
   * @param loc the location tracking object
   */
  public PeekStream(Location<T> loc) {
    initLoc = loc;
    markedStack = null;
    
    // The constructor cannnot call read() because the subclass is not init
    buffer = nextElement = null;
  }

  /**
   * Returns the next element in the stream, or {@code null} if beyond its end. 
   * @return the next element in the stream
   * @throws IOException if thrown by underlying stream
   */
  public T next() throws IOException {
    if (buffer == null) {
      ElLocPair x = new ElLocPair(read(), initLoc);
      buffer = nextElement = new Node<ElLocPair>(x);
    }
    if (nextElement.data.elem == null) return null;
    T result = nextElement.data.elem;
    if (nextElement.next == null) {
      Location<T> l = nextElement.data.loc.advance(result);
      ElLocPair x = new ElLocPair(read(), l);
      nextElement.next = new Node<ElLocPair>(x);
    }
    nextElement = nextElement.next;
    return result;
  }
  
  /**
   * Marks the current position (if not already marked).
   * @see freeboogie.ast.gen.PeekStream#rewind()
   */
  public void mark() {
    if (markedStack != null && markedStack.data == nextElement) return;
    markedStack = new Node<Node<ElLocPair>>(nextElement, markedStack);
  }
  
  /**
   * Go back to the previously marked element or to the beginning of 
   * the (not-yet-eaten) stream if no element is marked.
   */
  public void rewind() {
    if (markedStack == null) nextElement = buffer;
    else {
      nextElement = markedStack.data;
      markedStack = markedStack.next;
    }
  }
  
  /**
   * Eats the elements from the beginning up to, and including, the
   * last element read by {@code next}. 
   */
  public void eat() {
    while (buffer != nextElement) {
      if (markedStack != null && markedStack.data == buffer) 
        markedStack = markedStack.next;
      buffer = buffer.next;
    }
  }
  
  /**
   * Returns the location of the current element (that is, the one before
   * what {@code next} would return). If {@code next} was not called then
   * return the location object given to the constructor.
   * @return the location in the stream
   */
  public Location<T> getLoc() {
    if (buffer == null) return initLoc;
    return nextElement.data.loc;
  }
  
  /**
   * Reads one element from the underlying stream. Must return {@code null}
   * if the end was reached.
   * @return the next element in the underlying stream
   * @throws IOException if thrown by the underlying stream
   */
  protected abstract T read() throws IOException; 
}
