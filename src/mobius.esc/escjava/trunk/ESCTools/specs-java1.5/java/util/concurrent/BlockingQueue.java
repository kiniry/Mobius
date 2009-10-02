package java.util.concurrent;

import java.util.Collection;
import java.util.Queue;

public interface BlockingQueue extends Queue {
    
    boolean offer(Object o);
    
    boolean offer(Object o, long timeout, TimeUnit unit) throws InterruptedException;
    
    Object poll(long timeout, TimeUnit unit) throws InterruptedException;
    
    Object take() throws InterruptedException;
    
    void put(Object o) throws InterruptedException;
    
    int remainingCapacity();
    
    boolean add(Object o);
    
    int drainTo(Collection c);
    
    int drainTo(Collection c, int maxElements);
}
