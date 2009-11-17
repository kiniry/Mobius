package java.awt;

abstract class MediaEntry {
    MediaTracker tracker;
    int ID;
    MediaEntry next;
    int status;
    boolean cancelled;
    
    MediaEntry(MediaTracker mt, int id) {
        
        tracker = mt;
        ID = id;
    }
    
    abstract Object getMedia();
    
    static MediaEntry insert(MediaEntry head, MediaEntry me) {
        MediaEntry cur = head;
        MediaEntry prev = null;
        while (cur != null) {
            if (cur.ID > me.ID) {
                break;
            }
            prev = cur;
            cur = cur.next;
        }
        me.next = cur;
        if (prev == null) {
            head = me;
        } else {
            prev.next = me;
        }
        return head;
    }
    
    int getID() {
        return ID;
    }
    
    abstract void startLoad();
    
    void cancel() {
        cancelled = true;
    }
    static final int LOADING = MediaTracker.LOADING;
    static final int ABORTED = MediaTracker.ABORTED;
    static final int ERRORED = MediaTracker.ERRORED;
    static final int COMPLETE = MediaTracker.COMPLETE;
    static final int LOADSTARTED = (LOADING | ERRORED | COMPLETE);
    static final int DONE = (ABORTED | ERRORED | COMPLETE);
    
    synchronized int getStatus(boolean doLoad, boolean doVerify) {
        if (doLoad && ((status & LOADSTARTED) == 0)) {
            status = (status & ~ABORTED) | LOADING;
            startLoad();
        }
        return status;
    }
    
    void setStatus(int flag) {
        synchronized (this) {
            status = flag;
        }
        tracker.setDone();
    }
}
