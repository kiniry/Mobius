/** Public domain. */

package freeboogie.ast.gen;

import java.io.IOException;

/** A singly-list node. */
class Node<T> {
  /** data */  public T data;
  /** next */ public Node<T> next;
  
  /**
   * Initializes a node to put at the end of the list.
   * @param data the data to put in the node
   */
  public Node(T data) {
    this.data = data;
    this.next = null;
  }
}

/**
 * Provides a next-rewind-eat interface. 
 * 
 * @author rgrig 
 * @author reviewed by TODO
 * @param <T> the type of the stream elements
 */
public abstract class PeekStream<T> {
  /*
   * TODO The method PeekStream.rewind is never used, probably because
   * the grammar is (almost) LL(1). Does this mean that I should get rid
   * of all this buffering stuff?
   */
  
  
  /*
   * These variables refer to the {@code head}, {@code last} element,
   * and {@code len}gth of a singly linked list that acts as a buffer.
   */
  private Node<T> head;
  private Node<T> last;
  private int len;
  
  private Node<T> curNode; // curNode.data is what next() will return when called
  private int curPos;      // 0-based index in the list
  
  private Location<T> loc;
  
  /*
   * This rather ugly initialization trick is here to ensure that the
   * constructor does not throw any exception. (TODO change this?)
   */
  private boolean initialized;
  
  /**
   * Creates a {@code PeekStream} and sets a location tracking object.
   * @param loc the location tracking object
   */
  public PeekStream(Location<T> loc) {
    this.loc = loc;
    initialized = false;
  }

  private void init() throws IOException {
    head = last = curNode = new Node<T>(read());
    curPos = 0;
    len = 1;
    initialized = true;
  }
  
  /**
   * Returns the next element in the stream, or {@code null} if beyond. 
   * @return the next element in the stream
   * @throws IOException if thrown by underlying stream
   */
  public T next() throws IOException {
    if (!initialized) init();
    if (curPos == len - 1) {
      if (curNode.data == null) return null;
      last.next = new Node<T>(read());
      last = last.next;
      ++len;
    }
    T result = curNode.data;
    curNode = curNode.next;
    ++curPos;
    return result;
  }
  
  /**
   * Go back to the begining of the (non-yet-eaten) stream.
   * @throws IOException if thrown by the underlying stream
   */
  public void rewind() throws IOException {
    if (!initialized) init();
    curPos = 0;
    curNode = head;
  }
  
  /**
   * Eats the elements from the beginning up to, and including, the
   * last element read by {@code next}. 
   * @throws IOException if thrown by the underlying stream
   */
  public void eat() throws IOException {
    if (!initialized) init();
    while (head != curNode) {
      loc.advance(head.data);
      head = head.next;
    }
    len -= curPos;
    curPos = 0;
  }
  
  /**
   * Returns the location in the stream of the first uneaten element.
   * @return the location in the stream
   */
  public Location<T> getLoc() {
    return loc;
  }
  
  /**
   * Reads one element from the underlying stream. Must return {@code null}
   * if the end was reached.
   * @return the next element in the underlying stream
   * @throws IOException if thrown by the underlying stream
   */
  public abstract T read() throws IOException; 
}
