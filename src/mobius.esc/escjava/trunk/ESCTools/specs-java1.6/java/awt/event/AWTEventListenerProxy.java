package java.awt.event;

import java.awt.AWTEvent;
import java.awt.event.AWTEventListener;

public class AWTEventListenerProxy extends java.util.EventListenerProxy implements AWTEventListener {
    private long eventMask;
    
    public AWTEventListenerProxy(long eventMask, AWTEventListener listener) {
        super(listener);
        this.eventMask = eventMask;
    }
    
    public void eventDispatched(AWTEvent evt) {
        ((AWTEventListener)(AWTEventListener)getListener()).eventDispatched(evt);
    }
    
    public long getEventMask() {
        return eventMask;
    }
}
