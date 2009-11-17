package java.awt.event;

import java.util.EventListener;

public interface HierarchyBoundsListener extends EventListener {
    
    public void ancestorMoved(HierarchyEvent e);
    
    public void ancestorResized(HierarchyEvent e);
}
