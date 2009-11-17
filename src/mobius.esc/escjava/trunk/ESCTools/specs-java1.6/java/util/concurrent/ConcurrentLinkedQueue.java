package java.util.concurrent;

import java.util.*;
import java.util.concurrent.atomic.*;

public class ConcurrentLinkedQueue extends AbstractQueue implements Queue, java.io.Serializable {
    private static final long serialVersionUID = 196745693267521676L;
    {
    }
    private static final AtomicReferenceFieldUpdater tailUpdater = AtomicReferenceFieldUpdater.newUpdater(ConcurrentLinkedQueue.class, ConcurrentLinkedQueue.Node.class, "tail");
    private static final AtomicReferenceFieldUpdater headUpdater = AtomicReferenceFieldUpdater.newUpdater(ConcurrentLinkedQueue.class, ConcurrentLinkedQueue.Node.class, "head");
    
    private boolean casTail(ConcurrentLinkedQueue$Node cmp, ConcurrentLinkedQueue$Node val) {
        return tailUpdater.compareAndSet(this, cmp, val);
    }
    
    private boolean casHead(ConcurrentLinkedQueue$Node cmp, ConcurrentLinkedQueue$Node val) {
        return headUpdater.compareAndSet(this, cmp, val);
    }
    private volatile transient ConcurrentLinkedQueue$Node head = new ConcurrentLinkedQueue$Node(null, null);
    private volatile transient ConcurrentLinkedQueue$Node tail = head;
    
    public ConcurrentLinkedQueue() {
        
    }
    
    public ConcurrentLinkedQueue(Collection c) {
        
        for (Iterator it = c.iterator(); it.hasNext(); ) add(it.next());
    }
    
    public boolean add(Object o) {
        return offer(o);
    }
    
    public boolean offer(Object o) {
        if (o == null) throw new NullPointerException();
        ConcurrentLinkedQueue$Node n = new ConcurrentLinkedQueue$Node(o, null);
        for (; ; ) {
            ConcurrentLinkedQueue$Node t = tail;
            ConcurrentLinkedQueue$Node s = t.getNext();
            if (t == tail) {
                if (s == null) {
                    if (t.casNext(s, n)) {
                        casTail(t, n);
                        return true;
                    }
                } else {
                    casTail(t, s);
                }
            }
        }
    }
    
    public Object poll() {
        for (; ; ) {
            ConcurrentLinkedQueue$Node h = head;
            ConcurrentLinkedQueue$Node t = tail;
            ConcurrentLinkedQueue$Node first = h.getNext();
            if (h == head) {
                if (h == t) {
                    if (first == null) return null; else casTail(t, first);
                } else if (casHead(h, first)) {
                    Object item = first.getItem();
                    if (item != null) {
                        first.setItem(null);
                        return item;
                    }
                }
            }
        }
    }
    
    public Object peek() {
        for (; ; ) {
            ConcurrentLinkedQueue$Node h = head;
            ConcurrentLinkedQueue$Node t = tail;
            ConcurrentLinkedQueue$Node first = h.getNext();
            if (h == head) {
                if (h == t) {
                    if (first == null) return null; else casTail(t, first);
                } else {
                    Object item = first.getItem();
                    if (item != null) return item; else casHead(h, first);
                }
            }
        }
    }
    
    ConcurrentLinkedQueue$Node first() {
        for (; ; ) {
            ConcurrentLinkedQueue$Node h = head;
            ConcurrentLinkedQueue$Node t = tail;
            ConcurrentLinkedQueue$Node first = h.getNext();
            if (h == head) {
                if (h == t) {
                    if (first == null) return null; else casTail(t, first);
                } else {
                    if (first.getItem() != null) return first; else casHead(h, first);
                }
            }
        }
    }
    
    public boolean isEmpty() {
        return first() == null;
    }
    
    public int size() {
        int count = 0;
        for (ConcurrentLinkedQueue$Node p = first(); p != null; p = p.getNext()) {
            if (p.getItem() != null) {
                if (++count == Integer.MAX_VALUE) break;
            }
        }
        return count;
    }
    
    public boolean contains(Object o) {
        if (o == null) return false;
        for (ConcurrentLinkedQueue$Node p = first(); p != null; p = p.getNext()) {
            Object item = p.getItem();
            if (item != null && o.equals(item)) return true;
        }
        return false;
    }
    
    public boolean remove(Object o) {
        if (o == null) return false;
        for (ConcurrentLinkedQueue$Node p = first(); p != null; p = p.getNext()) {
            Object item = p.getItem();
            if (item != null && o.equals(item) && p.casItem(item, null)) return true;
        }
        return false;
    }
    
    public Object[] toArray() {
        ArrayList al = new ArrayList();
        for (ConcurrentLinkedQueue$Node p = first(); p != null; p = p.getNext()) {
            Object item = p.getItem();
            if (item != null) al.add(item);
        }
        return al.toArray();
    }
    
    public Object[] toArray(Object[] a) {
        int k = 0;
        ConcurrentLinkedQueue$Node p;
        for (p = first(); p != null && k < a.length; p = p.getNext()) {
            Object item = p.getItem();
            if (item != null) a[k++] = (Object)item;
        }
        if (p == null) {
            if (k < a.length) a[k] = null;
            return a;
        }
        ArrayList al = new ArrayList();
        for (ConcurrentLinkedQueue$Node q = first(); q != null; q = q.getNext()) {
            Object item = q.getItem();
            if (item != null) al.add(item);
        }
        return (Object[])al.toArray(a);
    }
    
    public Iterator iterator() {
        return new ConcurrentLinkedQueue$Itr(this);
    }
    {
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        s.defaultWriteObject();
        for (ConcurrentLinkedQueue$Node p = first(); p != null; p = p.getNext()) {
            Object item = p.getItem();
            if (item != null) s.writeObject(item);
        }
        s.writeObject(null);
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        head = new ConcurrentLinkedQueue$Node(null, null);
        tail = head;
        for (; ; ) {
            Object item = (Object)s.readObject();
            if (item == null) break; else offer(item);
        }
    }
}
