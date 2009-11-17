package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.util.*;

class SystemEventQueueUtilities$RunnableEvent extends AWTEvent {
    static final int EVENT_ID = AWTEvent.RESERVED_ID_MAX + 1000;
    static final Component target = new SystemEventQueueUtilities$RunnableTarget();
    final Runnable doRun;
    final Object lock;
    Exception exception;
    
    SystemEventQueueUtilities$RunnableEvent(Runnable doRun, Object lock) {
        super(target, EVENT_ID);
        this.doRun = doRun;
        this.lock = lock;
    }
}
