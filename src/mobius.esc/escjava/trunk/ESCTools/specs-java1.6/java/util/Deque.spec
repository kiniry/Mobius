package java.util;
public interface Deque extends Queue {

    void addFirst(Object e);
    void addLast(Object e);
    boolean offerFirst(Object e);
    boolean offerLast(Object e);

    Object removeFirst();
    Object removeLast();


    Object pollFirst();

    Object pollLast();

    Object getFirst();

    Object getLast();

    Object peekFirst();

    Object peekLast();

    boolean removeFirstOccurrence(Object o);

    boolean removeLastOccurrence(Object o);

    boolean add(Object e);

    boolean offer(Object e);

    Object remove();
    Object poll();
    Object element();
    Object peek();

    void push(Object e);

    Object pop();

    boolean remove(Object o);
    boolean contains(Object o);

    public int size();


    /*@ non_null @*/ Iterator iterator();
    Iterator descendingIterator();

}