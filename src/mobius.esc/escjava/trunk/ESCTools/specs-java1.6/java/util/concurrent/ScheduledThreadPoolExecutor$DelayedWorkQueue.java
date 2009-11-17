package java.util.concurrent;

import java.util.concurrent.atomic.*;
import java.util.*;

class ScheduledThreadPoolExecutor$DelayedWorkQueue extends AbstractCollection implements BlockingQueue {
    
    /*synthetic*/ static DelayQueue access$500(ScheduledThreadPoolExecutor$DelayedWorkQueue x0) {
        return x0.dq;
    }
    
    /*synthetic*/ ScheduledThreadPoolExecutor$DelayedWorkQueue(java.util.concurrent.ScheduledThreadPoolExecutor$1 x0) {
        this();
    }
    
    private ScheduledThreadPoolExecutor$DelayedWorkQueue() {
        
    }
    private final DelayQueue dq = new DelayQueue();
    
    public Runnable poll() {
        return (Runnable)dq.poll();
    }
    
    public Runnable peek() {
        return (Runnable)dq.peek();
    }
    
    public Runnable take() throws InterruptedException {
        return (Runnable)dq.take();
    }
    
    public Runnable poll(long timeout, TimeUnit unit) throws InterruptedException {
        return (Runnable)dq.poll(timeout, unit);
    }
    
    public boolean add(Runnable x) {
        return dq.add((ScheduledThreadPoolExecutor$ScheduledFutureTask)(ScheduledThreadPoolExecutor$ScheduledFutureTask)x);
    }
    
    public boolean offer(Runnable x) {
        return dq.offer((ScheduledThreadPoolExecutor$ScheduledFutureTask)(ScheduledThreadPoolExecutor$ScheduledFutureTask)x);
    }
    
    public void put(Runnable x) {
        dq.put((ScheduledThreadPoolExecutor$ScheduledFutureTask)(ScheduledThreadPoolExecutor$ScheduledFutureTask)x);
    }
    
    public boolean offer(Runnable x, long timeout, TimeUnit unit) {
        return dq.offer((ScheduledThreadPoolExecutor$ScheduledFutureTask)(ScheduledThreadPoolExecutor$ScheduledFutureTask)x, timeout, unit);
    }
    
    public Runnable remove() {
        return (Runnable)dq.remove();
    }
    
    public Runnable element() {
        return (Runnable)dq.element();
    }
    
    public void clear() {
        dq.clear();
    }
    
    public int drainTo(Collection c) {
        return dq.drainTo(c);
    }
    
    public int drainTo(Collection c, int maxElements) {
        return dq.drainTo(c, maxElements);
    }
    
    public int remainingCapacity() {
        return dq.remainingCapacity();
    }
    
    public boolean remove(Object x) {
        return dq.remove(x);
    }
    
    public boolean contains(Object x) {
        return dq.contains(x);
    }
    
    public int size() {
        return dq.size();
    }
    
    public boolean isEmpty() {
        return dq.isEmpty();
    }
    
    public Object[] toArray() {
        return dq.toArray();
    }
    
    public Object[] toArray(Object[] array) {
        return dq.toArray(array);
    }
    
    public Iterator iterator() {
        return new ScheduledThreadPoolExecutor$DelayedWorkQueue$1(this);
    }
    
    /*synthetic*/ public boolean add(Object x0) {
        return this.add((Runnable)x0);
    }
    
    /*synthetic*/ public void put(Object x0) throws InterruptedException {
        this.put((Runnable)x0);
    }
    
    /*synthetic public Object take() throws InterruptedException {
        return this.take();
    } */
    
    /*synthetic  public Object poll(long x0, TimeUnit x1) throws InterruptedException {
        return this.poll(x0, x1);
    } */
    
    /*synthetic*/ public boolean offer(Object x0, long x1, TimeUnit x2) throws InterruptedException {
        return this.offer((Runnable)x0, x1, x2);
    }
    
    /*synthetic*/ public boolean offer(Object x0) {
        return this.offer((Runnable)x0);
    }
    
    /*synthetic public Object element() {
        return this.element();
    } */
    
    /*synthetic public Object peek() {
        return this.peek();
    } */
    
    /*synthetic public Object remove() {
        return this.remove();
    } */
    
    /*synthetic public Object poll() {
        return this.poll();
    } */
}
