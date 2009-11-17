package java.awt.dnd;

import java.util.EventListener;

public interface DragSourceListener extends EventListener {
    
    void dragEnter(DragSourceDragEvent dsde);
    
    void dragOver(DragSourceDragEvent dsde);
    
    void dropActionChanged(DragSourceDragEvent dsde);
    
    void dragExit(DragSourceEvent dse);
    
    void dragDropEnd(DragSourceDropEvent dsde);
}
