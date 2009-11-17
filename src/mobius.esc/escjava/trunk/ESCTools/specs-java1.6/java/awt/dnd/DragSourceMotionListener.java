package java.awt.dnd;

import java.util.EventListener;

public interface DragSourceMotionListener extends EventListener {
    
    void dragMouseMoved(DragSourceDragEvent dsde);
}
