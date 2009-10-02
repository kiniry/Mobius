package java.awt;

import javax.accessibility.*;

class Container$MouseEventTargetFilter implements Container$EventTargetFilter {
    static final Container$EventTargetFilter FILTER = new Container$MouseEventTargetFilter();
    
    private Container$MouseEventTargetFilter() {
        
    }
    
    public boolean accept(final Component comp) {
        return (comp.eventMask & AWTEvent.MOUSE_MOTION_EVENT_MASK) != 0 || (comp.eventMask & AWTEvent.MOUSE_EVENT_MASK) != 0 || (comp.eventMask & AWTEvent.MOUSE_WHEEL_EVENT_MASK) != 0 || comp.mouseListener != null || comp.mouseMotionListener != null || comp.mouseWheelListener != null;
    }
}
