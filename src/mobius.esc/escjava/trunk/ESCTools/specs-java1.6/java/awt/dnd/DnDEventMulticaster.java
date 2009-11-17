package java.awt.dnd;

import java.awt.AWTEventMulticaster;
import java.util.EventListener;
import java.io.ObjectOutputStream;
import java.io.IOException;
import java.util.EventListener;

class DnDEventMulticaster extends AWTEventMulticaster implements DragSourceListener, DragSourceMotionListener {
    
    protected DnDEventMulticaster(EventListener a, EventListener b) {
        super(a, b);
    }
    
    public void dragEnter(DragSourceDragEvent dsde) {
        ((DragSourceListener)(DragSourceListener)a).dragEnter(dsde);
        ((DragSourceListener)(DragSourceListener)b).dragEnter(dsde);
    }
    
    public void dragOver(DragSourceDragEvent dsde) {
        ((DragSourceListener)(DragSourceListener)a).dragOver(dsde);
        ((DragSourceListener)(DragSourceListener)b).dragOver(dsde);
    }
    
    public void dropActionChanged(DragSourceDragEvent dsde) {
        ((DragSourceListener)(DragSourceListener)a).dropActionChanged(dsde);
        ((DragSourceListener)(DragSourceListener)b).dropActionChanged(dsde);
    }
    
    public void dragExit(DragSourceEvent dse) {
        ((DragSourceListener)(DragSourceListener)a).dragExit(dse);
        ((DragSourceListener)(DragSourceListener)b).dragExit(dse);
    }
    
    public void dragDropEnd(DragSourceDropEvent dsde) {
        ((DragSourceListener)(DragSourceListener)a).dragDropEnd(dsde);
        ((DragSourceListener)(DragSourceListener)b).dragDropEnd(dsde);
    }
    
    public void dragMouseMoved(DragSourceDragEvent dsde) {
        ((DragSourceMotionListener)(DragSourceMotionListener)a).dragMouseMoved(dsde);
        ((DragSourceMotionListener)(DragSourceMotionListener)b).dragMouseMoved(dsde);
    }
    
    public static DragSourceListener add(DragSourceListener a, DragSourceListener b) {
        return (DragSourceListener)(DragSourceListener)addInternal(a, b);
    }
    
    public static DragSourceMotionListener add(DragSourceMotionListener a, DragSourceMotionListener b) {
        return (DragSourceMotionListener)(DragSourceMotionListener)addInternal(a, b);
    }
    
    public static DragSourceListener remove(DragSourceListener l, DragSourceListener oldl) {
        return (DragSourceListener)(DragSourceListener)removeInternal(l, oldl);
    }
    
    public static DragSourceMotionListener remove(DragSourceMotionListener l, DragSourceMotionListener ol) {
        return (DragSourceMotionListener)(DragSourceMotionListener)removeInternal(l, ol);
    }
    
    protected static EventListener addInternal(EventListener a, EventListener b) {
        if (a == null) return b;
        if (b == null) return a;
        return new DnDEventMulticaster(a, b);
    }
    
    protected EventListener remove(EventListener oldl) {
        if (oldl == a) return b;
        if (oldl == b) return a;
        EventListener a2 = removeInternal(a, oldl);
        EventListener b2 = removeInternal(b, oldl);
        if (a2 == a && b2 == b) {
            return this;
        }
        return addInternal(a2, b2);
    }
    
    protected static EventListener removeInternal(EventListener l, EventListener oldl) {
        if (l == oldl || l == null) {
            return null;
        } else if (l instanceof DnDEventMulticaster) {
            return ((DnDEventMulticaster)(DnDEventMulticaster)l).remove(oldl);
        } else {
            return l;
        }
    }
    
    protected static void save(ObjectOutputStream s, String k, EventListener l) throws IOException {
        AWTEventMulticaster.save(s, k, l);
    }
}
