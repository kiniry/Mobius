package freeboogie.util;

import java.util.ArrayDeque;
import java.util.Deque;

/** A stack of stacks. */
public class FramedStack<T> {
  private Deque<Deque<T>> data;

  public FramedStack() {
    data = new ArrayDeque<Deque<T>>();
    data.addFirst(new ArrayDeque<T>());
  }

  public void push(T element) {
    data.peekFirst().addFirst(element);
  }

  public T pop() {
    return data.peekFirst().removeFirst();
  }

  public void pushFrame() {
    data.addFirst(new ArrayDeque<T>());
  }

  public Deque<T> popFrame() {
    return data.removeFirst();
  }
}
