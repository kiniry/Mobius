package java.awt;

import java.awt.dnd.DropTarget;
import javax.accessibility.*;

class Container$DropTargetEventTargetFilter implements Container$EventTargetFilter {
    static final Container$EventTargetFilter FILTER = new Container$DropTargetEventTargetFilter();
    
    private Container$DropTargetEventTargetFilter() {
        
    }
    
    public boolean accept(final Component comp) {
        DropTarget dt = comp.getDropTarget();
        return dt != null && dt.isActive();
    }
}
