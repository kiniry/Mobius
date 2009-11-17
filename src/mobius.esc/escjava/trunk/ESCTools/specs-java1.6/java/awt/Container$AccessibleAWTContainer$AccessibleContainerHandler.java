package java.awt;

import java.awt.event.ContainerEvent;
import java.awt.event.ContainerListener;
import javax.accessibility.*;

public class Container$AccessibleAWTContainer$AccessibleContainerHandler implements ContainerListener {
    /*synthetic*/ final Container$AccessibleAWTContainer this$1;
    
    protected Container$AccessibleAWTContainer$AccessibleContainerHandler(/*synthetic*/ final Container$AccessibleAWTContainer this$1) {
        this.this$1 = this$1;
        
    }
    
    public void componentAdded(ContainerEvent e) {
        Component c = e.getChild();
        if (c != null && c instanceof Accessible) {
            this$1.firePropertyChange(AccessibleContext.ACCESSIBLE_CHILD_PROPERTY, null, ((Accessible)(Accessible)c).getAccessibleContext());
        }
    }
    
    public void componentRemoved(ContainerEvent e) {
        Component c = e.getChild();
        if (c != null && c instanceof Accessible) {
            this$1.firePropertyChange(AccessibleContext.ACCESSIBLE_CHILD_PROPERTY, ((Accessible)(Accessible)c).getAccessibleContext(), null);
        }
    }
}
