package java.awt.dnd;

import java.util.EventListener;

public interface DragGestureListener extends EventListener {
    
    void dragGestureRecognized(DragGestureEvent dge);
}
