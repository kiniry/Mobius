package java.lang.ref;

import sun.misc.Cleaner;

class Reference$ReferenceHandler extends Thread {
    
    Reference$ReferenceHandler(ThreadGroup g, String name) {
        super(g, name);
    }
    
    public void run() {
        for (; ; ) {
            Reference r;
            synchronized (Reference.access$100()) {
                if (Reference.access$200() != null) {
                    r = Reference.access$200();
                    Reference rn = r.next;
                    Reference.access$202((rn == r) ? null : rn);
                    r.next = r;
                } else {
                    try {
                        Reference.access$100().wait();
                    } catch (InterruptedException x) {
                    }
                    continue;
                }
            }
            if (r instanceof Cleaner) {
                ((Cleaner)(Cleaner)r).clean();
                continue;
            }
            ReferenceQueue q = r.queue;
            if (q != ReferenceQueue.NULL) q.enqueue(r);
        }
    }
}
