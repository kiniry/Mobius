package java.awt;

import java.awt.event.*;
import javax.accessibility.*;
import javax.accessibility.*;
import java.util.logging.*;

public class Component$AccessibleAWTComponent$AccessibleAWTFocusHandler implements FocusListener {
    /*synthetic*/ final Component$AccessibleAWTComponent this$1;
    
    protected Component$AccessibleAWTComponent$AccessibleAWTFocusHandler(/*synthetic*/ final Component$AccessibleAWTComponent this$1) {
        this.this$1 = this$1;
        
    }
    
    public void focusGained(FocusEvent event) {
        if (this$1.this$0.accessibleContext != null) {
            this$1.this$0.accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.FOCUSED);
        }
    }
    
    public void focusLost(FocusEvent event) {
        if (this$1.this$0.accessibleContext != null) {
            this$1.this$0.accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.FOCUSED, null);
        }
    }
}
