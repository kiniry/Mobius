package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.util.*;

class SystemEventQueueUtilities$TimerQueueRestart implements Runnable {
    
    /*synthetic*/ SystemEventQueueUtilities$TimerQueueRestart(javax.swing.SystemEventQueueUtilities$1 x0) {
        this();
    }
    
    private SystemEventQueueUtilities$TimerQueueRestart() {
        
    }
    boolean attemptedStart;
    
    public synchronized void run() {
        if (!attemptedStart) {
            TimerQueue q = TimerQueue.sharedInstance();
            synchronized (q) {
                if (!q.running) q.start();
            }
            attemptedStart = true;
        }
    }
}
