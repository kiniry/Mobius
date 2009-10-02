package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

final class SynchronousQueue$LifoWaitQueue extends SynchronousQueue$WaitQueue implements java.io.Serializable {
    
    SynchronousQueue$LifoWaitQueue() {
        
    }
    private static final long serialVersionUID = -3633113410248163686L;
    private transient SynchronousQueue$Node head;
    
    SynchronousQueue$Node enq(Object x) {
        return head = new SynchronousQueue$Node(x, head);
    }
    
    SynchronousQueue$Node deq() {
        SynchronousQueue$Node p = head;
        if (p != null) {
            head = p.next;
            p.next = null;
        }
        return p;
    }
}
