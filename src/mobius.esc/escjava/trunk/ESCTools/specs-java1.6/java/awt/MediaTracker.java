package java.awt;

import java.awt.Component;
import java.awt.Image;

public class MediaTracker implements java.io.Serializable {
    Component target;
    MediaEntry head;
    private static final long serialVersionUID = -483174189758638095L;
    
    public MediaTracker(Component comp) {
        
        target = comp;
    }
    
    public void addImage(Image image, int id) {
        addImage(image, id, -1, -1);
    }
    
    public synchronized void addImage(Image image, int id, int w, int h) {
        head = MediaEntry.insert(head, new ImageMediaEntry(this, image, id, w, h));
    }
    public static final int LOADING = 1;
    public static final int ABORTED = 2;
    public static final int ERRORED = 4;
    public static final int COMPLETE = 8;
    static final int DONE = (ABORTED | ERRORED | COMPLETE);
    
    public boolean checkAll() {
        return checkAll(false, true);
    }
    
    public boolean checkAll(boolean load) {
        return checkAll(load, true);
    }
    
    private synchronized boolean checkAll(boolean load, boolean verify) {
        MediaEntry cur = head;
        boolean done = true;
        while (cur != null) {
            if ((cur.getStatus(load, verify) & DONE) == 0) {
                done = false;
            }
            cur = cur.next;
        }
        return done;
    }
    
    public synchronized boolean isErrorAny() {
        MediaEntry cur = head;
        while (cur != null) {
            if ((cur.getStatus(false, true) & ERRORED) != 0) {
                return true;
            }
            cur = cur.next;
        }
        return false;
    }
    
    public synchronized Object[] getErrorsAny() {
        MediaEntry cur = head;
        int numerrors = 0;
        while (cur != null) {
            if ((cur.getStatus(false, true) & ERRORED) != 0) {
                numerrors++;
            }
            cur = cur.next;
        }
        if (numerrors == 0) {
            return null;
        }
        Object[] errors = new Object[numerrors];
        cur = head;
        numerrors = 0;
        while (cur != null) {
            if ((cur.getStatus(false, false) & ERRORED) != 0) {
                errors[numerrors++] = cur.getMedia();
            }
            cur = cur.next;
        }
        return errors;
    }
    
    public void waitForAll() throws InterruptedException {
        waitForAll(0);
    }
    
    public synchronized boolean waitForAll(long ms) throws InterruptedException {
        long end = System.currentTimeMillis() + ms;
        boolean first = true;
        while (true) {
            int status = statusAll(first, first);
            if ((status & LOADING) == 0) {
                return (status == COMPLETE);
            }
            first = false;
            long timeout;
            if (ms == 0) {
                timeout = 0;
            } else {
                timeout = end - System.currentTimeMillis();
                if (timeout <= 0) {
                    return false;
                }
            }
            wait(timeout);
        }
    }
    
    public int statusAll(boolean load) {
        return statusAll(load, true);
    }
    
    private synchronized int statusAll(boolean load, boolean verify) {
        MediaEntry cur = head;
        int status = 0;
        while (cur != null) {
            status = status | cur.getStatus(load, verify);
            cur = cur.next;
        }
        return status;
    }
    
    public boolean checkID(int id) {
        return checkID(id, false, true);
    }
    
    public boolean checkID(int id, boolean load) {
        return checkID(id, load, true);
    }
    
    private synchronized boolean checkID(int id, boolean load, boolean verify) {
        MediaEntry cur = head;
        boolean done = true;
        while (cur != null) {
            if (cur.getID() == id && (cur.getStatus(load, verify) & DONE) == 0) {
                done = false;
            }
            cur = cur.next;
        }
        return done;
    }
    
    public synchronized boolean isErrorID(int id) {
        MediaEntry cur = head;
        while (cur != null) {
            if (cur.getID() == id && (cur.getStatus(false, true) & ERRORED) != 0) {
                return true;
            }
            cur = cur.next;
        }
        return false;
    }
    
    public synchronized Object[] getErrorsID(int id) {
        MediaEntry cur = head;
        int numerrors = 0;
        while (cur != null) {
            if (cur.getID() == id && (cur.getStatus(false, true) & ERRORED) != 0) {
                numerrors++;
            }
            cur = cur.next;
        }
        if (numerrors == 0) {
            return null;
        }
        Object[] errors = new Object[numerrors];
        cur = head;
        numerrors = 0;
        while (cur != null) {
            if (cur.getID() == id && (cur.getStatus(false, false) & ERRORED) != 0) {
                errors[numerrors++] = cur.getMedia();
            }
            cur = cur.next;
        }
        return errors;
    }
    
    public void waitForID(int id) throws InterruptedException {
        waitForID(id, 0);
    }
    
    public synchronized boolean waitForID(int id, long ms) throws InterruptedException {
        long end = System.currentTimeMillis() + ms;
        boolean first = true;
        while (true) {
            int status = statusID(id, first, first);
            if ((status & LOADING) == 0) {
                return (status == COMPLETE);
            }
            first = false;
            long timeout;
            if (ms == 0) {
                timeout = 0;
            } else {
                timeout = end - System.currentTimeMillis();
                if (timeout <= 0) {
                    return false;
                }
            }
            wait(timeout);
        }
    }
    
    public int statusID(int id, boolean load) {
        return statusID(id, load, true);
    }
    
    private synchronized int statusID(int id, boolean load, boolean verify) {
        MediaEntry cur = head;
        int status = 0;
        while (cur != null) {
            if (cur.getID() == id) {
                status = status | cur.getStatus(load, verify);
            }
            cur = cur.next;
        }
        return status;
    }
    
    public synchronized void removeImage(Image image) {
        MediaEntry cur = head;
        MediaEntry prev = null;
        while (cur != null) {
            MediaEntry next = cur.next;
            if (cur.getMedia() == image) {
                if (prev == null) {
                    head = next;
                } else {
                    prev.next = next;
                }
                cur.cancel();
            } else {
                prev = cur;
            }
            cur = next;
        }
        notifyAll();
    }
    
    public synchronized void removeImage(Image image, int id) {
        MediaEntry cur = head;
        MediaEntry prev = null;
        while (cur != null) {
            MediaEntry next = cur.next;
            if (cur.getID() == id && cur.getMedia() == image) {
                if (prev == null) {
                    head = next;
                } else {
                    prev.next = next;
                }
                cur.cancel();
            } else {
                prev = cur;
            }
            cur = next;
        }
        notifyAll();
    }
    
    public synchronized void removeImage(Image image, int id, int width, int height) {
        MediaEntry cur = head;
        MediaEntry prev = null;
        while (cur != null) {
            MediaEntry next = cur.next;
            if (cur.getID() == id && cur instanceof ImageMediaEntry && ((ImageMediaEntry)(ImageMediaEntry)cur).matches(image, width, height)) {
                if (prev == null) {
                    head = next;
                } else {
                    prev.next = next;
                }
                cur.cancel();
            } else {
                prev = cur;
            }
            cur = next;
        }
        notifyAll();
    }
    
    synchronized void setDone() {
        notifyAll();
    }
}
