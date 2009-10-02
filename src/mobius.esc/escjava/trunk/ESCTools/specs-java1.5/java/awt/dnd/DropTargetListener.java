package java.awt.dnd;

import java.util.EventListener;
import java.awt.dnd.DropTargetDragEvent;
import java.awt.dnd.DropTargetDropEvent;

public interface DropTargetListener extends EventListener {
    
    void dragEnter(DropTargetDragEvent dtde);
    
    void dragOver(DropTargetDragEvent dtde);
    
    void dropActionChanged(DropTargetDragEvent dtde);
    
    void dragExit(DropTargetEvent dte);
    
    void drop(DropTargetDropEvent dtde);
}
