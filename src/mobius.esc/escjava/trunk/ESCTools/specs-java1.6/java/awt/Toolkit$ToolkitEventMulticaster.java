package java.awt;

import java.awt.event.*;
import java.awt.peer.*;
import java.awt.*;
import java.util.EventListener;

class Toolkit$ToolkitEventMulticaster extends AWTEventMulticaster implements AWTEventListener {
    
    Toolkit$ToolkitEventMulticaster(AWTEventListener a, AWTEventListener b) {
        super(a, b);
    }
    
    static AWTEventListener add(AWTEventListener a, AWTEventListener b) {
        if (a == null) return b;
        if (b == null) return a;
        return new Toolkit$ToolkitEventMulticaster(a, b);
    }
    
    static AWTEventListener remove(AWTEventListener l, AWTEventListener oldl) {
        return (AWTEventListener)(AWTEventListener)removeInternal(l, oldl);
    }
    
    protected EventListener remove(EventListener oldl) {
        if (oldl == a) return b;
        if (oldl == b) return a;
        AWTEventListener a2 = (AWTEventListener)(AWTEventListener)removeInternal(a, oldl);
        AWTEventListener b2 = (AWTEventListener)(AWTEventListener)removeInternal(b, oldl);
        if (a2 == a && b2 == b) {
            return this;
        }
        return add(a2, b2);
    }
    
    public void eventDispatched(AWTEvent event) {
        ((AWTEventListener)(AWTEventListener)a).eventDispatched(event);
        ((AWTEventListener)(AWTEventListener)b).eventDispatched(event);
    }
}
