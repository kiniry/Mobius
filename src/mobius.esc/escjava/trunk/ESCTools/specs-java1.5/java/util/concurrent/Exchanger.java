package java.util.concurrent;

import java.util.concurrent.atomic.*;
import java.util.concurrent.locks.LockSupport;

public class Exchanger {
    {
    }
    private static final int NCPU = Runtime.getRuntime().availableProcessors();
    private static final int CAPACITY = 32;
    private static final int FULL = Math.max(0, Math.min(CAPACITY, NCPU / 2) - 1);
    private static final int SPINS = (NCPU == 1) ? 0 : 2000;
    private static final int TIMED_SPINS = SPINS / 20;
    private static final Object CANCEL = new Object();
    private static final Object NULL_ITEM = new Object();
    {
    }
    {
    }
    private volatile Exchanger$Slot[] arena = new Exchanger$Slot[CAPACITY];
    private final AtomicInteger max = new AtomicInteger();
    
    private Object doExchange(Object item, boolean timed, long nanos) {
        Exchanger$Node me = new Exchanger$Node(item);
        int index = hashIndex();
        int fails = 0;
        for (; ; ) {
            Object y;
            Exchanger$Slot slot = arena[index];
            if (slot == null) createSlot(index); else if ((y = slot.get()) != null && slot.compareAndSet(y, null)) {
                Exchanger$Node you = (Exchanger$Node)(Exchanger$Node)y;
                if (you.compareAndSet(null, item)) {
                    LockSupport.unpark(you.waiter);
                    return you.item;
                }
            } else if (y == null && slot.compareAndSet(null, me)) {
                if (index == 0) return timed ? awaitNanos(me, slot, nanos) : await(me, slot);
                Object v = spinWait(me, slot);
                if (v != CANCEL) return v;
                me = new Exchanger$Node(item);
                int m = max.get();
                if (m > (index >>>= 1)) max.compareAndSet(m, m - 1);
            } else if (++fails > 1) {
                int m = max.get();
                if (fails > 3 && m < FULL && max.compareAndSet(m, m + 1)) index = m + 1; else if (--index < 0) index = m;
            }
        }
    }
    
    private final int hashIndex() {
        long id = Thread.currentThread().getId();
        int hash = (((int)(id ^ (id >>> 32))) ^ -2128831035) * 16777619;
        int m = max.get();
        int nbits = (((-1024 >> m) & 4) | ((504 >>> m) & 2) | ((-65294 >>> m) & 1));
        int index;
        while ((index = hash & ((1 << nbits) - 1)) > m) hash = (hash >>> nbits) | (hash << (33 - nbits));
        return index;
    }
    
    private void createSlot(int index) {
        Exchanger$Slot newSlot = new Exchanger$Slot(null);
        Exchanger$Slot[] a = arena;
        synchronized (a) {
            if (a[index] == null) a[index] = newSlot;
        }
    }
    
    private static boolean tryCancel(Exchanger$Node node, Exchanger$Slot slot) {
        if (!node.compareAndSet(null, CANCEL)) return false;
        if (slot.get() == node) slot.compareAndSet(node, null);
        return true;
    }
    
    private static Object spinWait(Exchanger$Node node, Exchanger$Slot slot) {
        int spins = SPINS;
        for (; ; ) {
            Object v = node.get();
            if (v != null) return v; else if (spins > 0) --spins; else tryCancel(node, slot);
        }
    }
    
    private static Object await(Exchanger$Node node, Exchanger$Slot slot) {
        Thread w = Thread.currentThread();
        int spins = SPINS;
        for (; ; ) {
            Object v = node.get();
            if (v != null) return v; else if (spins > 0) --spins; else if (node.waiter == null) node.waiter = w; else if (w.isInterrupted()) tryCancel(node, slot); else LockSupport.park();
        }
    }
    
    private Object awaitNanos(Exchanger$Node node, Exchanger$Slot slot, long nanos) {
        int spins = TIMED_SPINS;
        long lastTime = 0;
        Thread w = null;
        for (; ; ) {
            Object v = node.get();
            if (v != null) return v;
            long now = System.nanoTime();
            if (w == null) w = Thread.currentThread(); else nanos -= now - lastTime;
            lastTime = now;
            if (nanos > 0) {
                if (spins > 0) --spins; else if (node.waiter == null) node.waiter = w; else if (w.isInterrupted()) tryCancel(node, slot); else LockSupport.parkNanos(nanos);
            } else if (tryCancel(node, slot) && !w.isInterrupted()) return scanOnTimeout(node);
        }
    }
    
    private Object scanOnTimeout(Exchanger$Node node) {
        Object y;
        for (int j = arena.length - 1; j >= 0; --j) {
            Exchanger$Slot slot = arena[j];
            if (slot != null) {
                while ((y = slot.get()) != null) {
                    if (slot.compareAndSet(y, null)) {
                        Exchanger$Node you = (Exchanger$Node)(Exchanger$Node)y;
                        if (you.compareAndSet(null, node.item)) {
                            LockSupport.unpark(you.waiter);
                            return you.item;
                        }
                    }
                }
            }
        }
        return CANCEL;
    }
    
    public Exchanger() {
        
    }
    
    public Object exchange(Object x) throws InterruptedException {
        if (!Thread.interrupted()) {
            Object v = doExchange(x == null ? NULL_ITEM : x, false, 0);
            if (v == NULL_ITEM) return null;
            if (v != CANCEL) return (Object)v;
            Thread.interrupted();
        }
        throw new InterruptedException();
    }
    
    public Object exchange(Object x, long timeout, TimeUnit unit) throws InterruptedException, TimeoutException {
        if (!Thread.interrupted()) {
            Object v = doExchange(x == null ? NULL_ITEM : x, true, unit.toNanos(timeout));
            if (v == NULL_ITEM) return null;
            if (v != CANCEL) return (Object)v;
            if (!Thread.interrupted()) throw new TimeoutException();
        }
        throw new InterruptedException();
    }
}
