package java.awt;

import java.awt.event.*;
import javax.accessibility.*;
import javax.accessibility.*;
import java.util.logging.*;

public class Component$AccessibleAWTComponent$AccessibleAWTComponentHandler implements ComponentListener {
    /*synthetic*/ final Component$AccessibleAWTComponent this$1;
    
    protected Component$AccessibleAWTComponent$AccessibleAWTComponentHandler(/*synthetic*/ final Component$AccessibleAWTComponent this$1) {
        this.this$1 = this$1;
        
    }
    
    public void componentHidden(ComponentEvent e) {
        if (this$1.this$0.accessibleContext != null) {
            this$1.this$0.accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.VISIBLE, null);
        }
    }
    
    public void componentShown(ComponentEvent e) {
        if (this$1.this$0.accessibleContext != null) {
            this$1.this$0.accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.VISIBLE);
        }
    }
    
    public void componentMoved(ComponentEvent e) {
    }
    
    public void componentResized(ComponentEvent e) {
    }
}
