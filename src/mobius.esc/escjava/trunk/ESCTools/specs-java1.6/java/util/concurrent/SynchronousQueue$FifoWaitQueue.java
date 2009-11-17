package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

final class SynchronousQueue$FifoWaitQueue extends SynchronousQueue$WaitQueue implements java.io.Serializable {
    
    SynchronousQueue$FifoWaitQueue() {
        
    }
    private static final long serialVersionUID = -3623113410248163686L;
    private transient SynchronousQueue$Node head;
    private transient SynchronousQueue$Node last;
    
    SynchronousQueue$Node enq(Object x) {
        SynchronousQueue$Node p = new SynchronousQueue$Node(x);
        if (last == null) last = head = p; else last = last.next = p;
        return p;
    }
    
    SynchronousQueue$Node deq() {
        SynchronousQueue$Node p = head;
        if (p != null) {
            if ((head = p.next) == null) last = null;
            p.next = null;
        }
        return p;
    }
}
