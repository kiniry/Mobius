package java.awt;

import java.awt.event.*;
import java.awt.peer.*;
import java.awt.*;

class Toolkit$SelectiveAWTEventListener implements AWTEventListener {
    /*synthetic*/ final Toolkit this$0;
    AWTEventListener listener;
    private long eventMask;
    int[] calls = new int[64];
    
    public AWTEventListener getListener() {
        return listener;
    }
    
    public long getEventMask() {
        return eventMask;
    }
    
    public int[] getCalls() {
        return calls;
    }
    
    public void orEventMasks(long mask) {
        eventMask |= mask;
        for (int i = 0; i < 64; i++) {
            if (mask == 0) {
                break;
            }
            if ((mask & 1L) != 0) {
                calls[i]++;
            }
            mask >>>= 1;
        }
    }
    
    Toolkit$SelectiveAWTEventListener(/*synthetic*/ final Toolkit this$0, AWTEventListener l, long mask) {
        this.this$0 = this$0;
        
        listener = l;
        eventMask = mask;
    }
    
    public void eventDispatched(AWTEvent event) {
        long eventBit = 0;
        if (((eventBit = eventMask & AWTEvent.COMPONENT_EVENT_MASK) != 0 && event.id >= ComponentEvent.COMPONENT_FIRST && event.id <= ComponentEvent.COMPONENT_LAST) || ((eventBit = eventMask & AWTEvent.CONTAINER_EVENT_MASK) != 0 && event.id >= ContainerEvent.CONTAINER_FIRST && event.id <= ContainerEvent.CONTAINER_LAST) || ((eventBit = eventMask & AWTEvent.FOCUS_EVENT_MASK) != 0 && event.id >= FocusEvent.FOCUS_FIRST && event.id <= FocusEvent.FOCUS_LAST) || ((eventBit = eventMask & AWTEvent.KEY_EVENT_MASK) != 0 && event.id >= KeyEvent.KEY_FIRST && event.id <= KeyEvent.KEY_LAST) || ((eventBit = eventMask & AWTEvent.MOUSE_WHEEL_EVENT_MASK) != 0 && event.id == MouseEvent.MOUSE_WHEEL) || ((eventBit = eventMask & AWTEvent.MOUSE_MOTION_EVENT_MASK) != 0 && (event.id == MouseEvent.MOUSE_MOVED || event.id == MouseEvent.MOUSE_DRAGGED)) || ((eventBit = eventMask & AWTEvent.MOUSE_EVENT_MASK) != 0 && event.id != MouseEvent.MOUSE_MOVED && event.id != MouseEvent.MOUSE_DRAGGED && event.id != MouseEvent.MOUSE_WHEEL && event.id >= MouseEvent.MOUSE_FIRST && event.id <= MouseEvent.MOUSE_LAST) || ((eventBit = eventMask & AWTEvent.WINDOW_EVENT_MASK) != 0 && event.id >= WindowEvent.WINDOW_FIRST && event.id <= WindowEvent.WINDOW_LAST) || ((eventBit = eventMask & AWTEvent.ACTION_EVENT_MASK) != 0 && event.id >= ActionEvent.ACTION_FIRST && event.id <= ActionEvent.ACTION_LAST) || ((eventBit = eventMask & AWTEvent.ADJUSTMENT_EVENT_MASK) != 0 && event.id >= AdjustmentEvent.ADJUSTMENT_FIRST && event.id <= AdjustmentEvent.ADJUSTMENT_LAST) || ((eventBit = eventMask & AWTEvent.ITEM_EVENT_MASK) != 0 && event.id >= ItemEvent.ITEM_FIRST && event.id <= ItemEvent.ITEM_LAST) || ((eventBit = eventMask & AWTEvent.TEXT_EVENT_MASK) != 0 && event.id >= TextEvent.TEXT_FIRST && event.id <= TextEvent.TEXT_LAST) || ((eventBit = eventMask & AWTEvent.INPUT_METHOD_EVENT_MASK) != 0 && event.id >= InputMethodEvent.INPUT_METHOD_FIRST && event.id <= InputMethodEvent.INPUT_METHOD_LAST) || ((eventBit = eventMask & AWTEvent.PAINT_EVENT_MASK) != 0 && event.id >= PaintEvent.PAINT_FIRST && event.id <= PaintEvent.PAINT_LAST) || ((eventBit = eventMask & AWTEvent.INVOCATION_EVENT_MASK) != 0 && event.id >= InvocationEvent.INVOCATION_FIRST && event.id <= InvocationEvent.INVOCATION_LAST) || ((eventBit = eventMask & AWTEvent.HIERARCHY_EVENT_MASK) != 0 && event.id == HierarchyEvent.HIERARCHY_CHANGED) || ((eventBit = eventMask & AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK) != 0 && (event.id == HierarchyEvent.ANCESTOR_MOVED || event.id == HierarchyEvent.ANCESTOR_RESIZED)) || ((eventBit = eventMask & AWTEvent.WINDOW_STATE_EVENT_MASK) != 0 && event.id == WindowEvent.WINDOW_STATE_CHANGED) || ((eventBit = eventMask & AWTEvent.WINDOW_FOCUS_EVENT_MASK) != 0 && (event.id == WindowEvent.WINDOW_GAINED_FOCUS || event.id == WindowEvent.WINDOW_LOST_FOCUS))) {
            int ci = 0;
            for (long eMask = eventBit; eMask != 0; eMask >>>= 1, ci++) {
            }
            ci--;
            for (int i = 0; i < calls[ci]; i++) {
                listener.eventDispatched(event);
            }
        }
    }
}
