package javax.swing.text;

import javax.swing.event.*;

class DefaultStyledDocument$ChangeUpdateRunnable implements Runnable {
    /*synthetic*/ final DefaultStyledDocument this$0;
    
    DefaultStyledDocument$ChangeUpdateRunnable(/*synthetic*/ final DefaultStyledDocument this$0) {
        this.this$0 = this$0;
        
    }
    boolean isPending = false;
    
    public void run() {
        synchronized (this) {
            isPending = false;
        }
        try {
            this$0.writeLock();
            AbstractDocument$DefaultDocumentEvent dde = new AbstractDocument$DefaultDocumentEvent(this$0, 0, this$0.getLength(), DocumentEvent$EventType.CHANGE);
            dde.end();
            this$0.fireChangedUpdate(dde);
        } finally {
            this$0.writeUnlock();
        }
    }
}
