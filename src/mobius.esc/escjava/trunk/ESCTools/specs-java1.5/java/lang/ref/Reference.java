package java.lang.ref;

public abstract class Reference {
    
    /*synthetic*/ static Reference access$202(Reference x0) {
        return pending = x0;
    }
    
    /*synthetic*/ static Reference access$200() {
        return pending;
    }
    
    /*synthetic*/ static Reference$Lock access$100() {
        return lock;
    }
    {
    }
    private Object referent;
    ReferenceQueue queue;
    Reference next;
    private transient Reference discovered;
    {
    }
    {
    }
    private static Reference$Lock lock = new Reference$Lock(null);
    private static Reference pending = null;
    {
    }
    static {
        ThreadGroup tg = Thread.currentThread().getThreadGroup();
        for (ThreadGroup tgn = tg; tgn != null; tg = tgn, tgn = tg.getParent()) ;
        Thread handler = new Reference$ReferenceHandler(tg, "Reference Handler");
        handler.setPriority(Thread.MAX_PRIORITY);
        handler.setDaemon(true);
        handler.start();
    }
    
    public Object get() {
        return this.referent;
    }
    
    public void clear() {
        this.referent = null;
    }
    
    public boolean isEnqueued() {
        synchronized (this) {
            return (this.queue != ReferenceQueue.NULL) && (this.next != null);
        }
    }
    
    public boolean enqueue() {
        return this.queue.enqueue(this);
    }
    
    Reference(Object referent) {
        this(referent, null);
    }
    
    Reference(Object referent, ReferenceQueue queue) {
        
        this.referent = referent;
        this.queue = (queue == null) ? ReferenceQueue.NULL : queue;
    }
}
