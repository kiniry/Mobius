package java.awt.dnd;

import java.awt.Point;
import java.util.EventObject;

public class DragSourceEvent extends EventObject {
    private static final long serialVersionUID = -763287114604032641L;
    private final boolean locationSpecified;
    private final int x;
    private final int y;
    
    public DragSourceEvent(DragSourceContext dsc) {
        super(dsc);
        locationSpecified = false;
        this.x = 0;
        this.y = 0;
    }
    
    public DragSourceEvent(DragSourceContext dsc, int x, int y) {
        super(dsc);
        locationSpecified = true;
        this.x = x;
        this.y = y;
    }
    
    public DragSourceContext getDragSourceContext() {
        return (DragSourceContext)(DragSourceContext)getSource();
    }
    
    public Point getLocation() {
        if (locationSpecified) {
            return new Point(x, y);
        } else {
            return null;
        }
    }
    
    public int getX() {
        return x;
    }
    
    public int getY() {
        return y;
    }
}
