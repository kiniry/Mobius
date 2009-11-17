package java.awt.dnd.peer;

import java.awt.dnd.DropTarget;

public interface DropTargetPeer {
    
    void addDropTarget(DropTarget dt);
    
    void removeDropTarget(DropTarget dt);
}
