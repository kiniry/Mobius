package java.awt.event;

import java.awt.Component;
import java.awt.Rectangle;

public class PaintEvent extends ComponentEvent {
    public static final int PAINT_FIRST = 800;
    public static final int PAINT_LAST = 801;
    public static final int PAINT = PAINT_FIRST;
    public static final int UPDATE = PAINT_FIRST + 1;
    Rectangle updateRect;
    private static final long serialVersionUID = 1267492026433337593L;
    
    public PaintEvent(Component source, int id, Rectangle updateRect) {
        super(source, id);
        this.updateRect = updateRect;
    }
    
    public Rectangle getUpdateRect() {
        return updateRect;
    }
    
    public void setUpdateRect(Rectangle updateRect) {
        this.updateRect = updateRect;
    }
    
    public String paramString() {
        String typeStr;
        switch (id) {
        case PAINT: 
            typeStr = "PAINT";
            break;
        
        case UPDATE: 
            typeStr = "UPDATE";
            break;
        
        default: 
            typeStr = "unknown type";
        
        }
        return typeStr + ",updateRect=" + (updateRect != null ? updateRect.toString() : "null");
    }
}
