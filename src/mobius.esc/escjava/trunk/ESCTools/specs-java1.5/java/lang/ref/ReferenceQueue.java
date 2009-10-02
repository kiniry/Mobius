package java.lang.ref;

public class ReferenceQueue {
    {
    }
    
    public ReferenceQueue() {
        
    }
    {
    }
    static ReferenceQueue NULL = new ReferenceQueue$Null(null);
    static ReferenceQueue ENQUEUED = new ReferenceQueue$Null(null);
    {
    }
    {
    }
    private ReferenceQueue$Lock lock = new ReferenceQueue$Lock(null);
    private Reference head = null;
    private long queueLength = 0;
    private volatile boolean queueEmpty = true;
    
    boolean enqueue(Reference r) {
        synchronized (r) {
            if (r.queue == ENQUEUED) return false;
            synchronized (lock) {
                r.queue = ENQUEUED;
                r.next = (head == null) ? r : head;
                head = r;
                queueLength++;
                if (queueEmpty) queueEmpty = false;
                if (r instanceof FinalReference) {
                    sun.misc.VM.addFinalRefCount(1);
                }
                lock.notifyAll();
                return true;
            }
        }
    }
    
    private Reference reallyPoll() {
        if (head != null) {
            Reference r = head;
            head = (r.next == r) ? null : r.next;
            r.queue = NULL;
            r.next = r;
            queueLength--;
            if (queueLength <= 0) queueEmpty = true;
            if (r instanceof FinalReference) {
                sun.misc.VM.addFinalRefCount(-1);
            }
            return r;
        }
        return null;
    }
    
    public Reference poll() {
        if (queueEmpty) return null;
        synchronized (lock) {
            return reallyPoll();
        }
    }
    
    public Reference remove(long timeout) throws IllegalArgumentException, InterruptedException {
        if (timeout < 0) {
            throw new IllegalArgumentException("Negative timeout value");
        }
        synchronized (lock) {
            Reference r = reallyPoll();
            if (r != null) return r;
            for (; ; ) {
                lock.wait(timeout);
                r = reallyPoll();
                if (r != null) return r;
                if (timeout != 0) return null;
            }
        }
    }
    
    public Reference remove() throws InterruptedException {
        return remove(0);
    }
}
