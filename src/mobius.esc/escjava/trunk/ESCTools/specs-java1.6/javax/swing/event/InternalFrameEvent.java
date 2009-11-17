package javax.swing.event;

import java.awt.AWTEvent;
import javax.swing.JInternalFrame;

public class InternalFrameEvent extends AWTEvent {
    public static final int INTERNAL_FRAME_FIRST = 25549;
    public static final int INTERNAL_FRAME_LAST = 25555;
    public static final int INTERNAL_FRAME_OPENED = INTERNAL_FRAME_FIRST;
    public static final int INTERNAL_FRAME_CLOSING = 1 + INTERNAL_FRAME_FIRST;
    public static final int INTERNAL_FRAME_CLOSED = 2 + INTERNAL_FRAME_FIRST;
    public static final int INTERNAL_FRAME_ICONIFIED = 3 + INTERNAL_FRAME_FIRST;
    public static final int INTERNAL_FRAME_DEICONIFIED = 4 + INTERNAL_FRAME_FIRST;
    public static final int INTERNAL_FRAME_ACTIVATED = 5 + INTERNAL_FRAME_FIRST;
    public static final int INTERNAL_FRAME_DEACTIVATED = 6 + INTERNAL_FRAME_FIRST;
    
    public InternalFrameEvent(JInternalFrame source, int id) {
        super(source, id);
    }
    
    public String paramString() {
        String typeStr;
        switch (id) {
        case INTERNAL_FRAME_OPENED: 
            typeStr = "INTERNAL_FRAME_OPENED";
            break;
        
        case INTERNAL_FRAME_CLOSING: 
            typeStr = "INTERNAL_FRAME_CLOSING";
            break;
        
        case INTERNAL_FRAME_CLOSED: 
            typeStr = "INTERNAL_FRAME_CLOSED";
            break;
        
        case INTERNAL_FRAME_ICONIFIED: 
            typeStr = "INTERNAL_FRAME_ICONIFIED";
            break;
        
        case INTERNAL_FRAME_DEICONIFIED: 
            typeStr = "INTERNAL_FRAME_DEICONIFIED";
            break;
        
        case INTERNAL_FRAME_ACTIVATED: 
            typeStr = "INTERNAL_FRAME_ACTIVATED";
            break;
        
        case INTERNAL_FRAME_DEACTIVATED: 
            typeStr = "INTERNAL_FRAME_DEACTIVATED";
            break;
        
        default: 
            typeStr = "unknown type";
        
        }
        return typeStr;
    }
    
    public JInternalFrame getInternalFrame() {
        return (source instanceof JInternalFrame) ? (JInternalFrame)(JInternalFrame)source : null;
    }
}
