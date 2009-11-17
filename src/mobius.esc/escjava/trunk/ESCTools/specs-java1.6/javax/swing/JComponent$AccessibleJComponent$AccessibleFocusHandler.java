package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JComponent$AccessibleJComponent$AccessibleFocusHandler implements FocusListener {
    /*synthetic*/ final JComponent$AccessibleJComponent this$1;
    
    protected JComponent$AccessibleJComponent$AccessibleFocusHandler(/*synthetic*/ final JComponent$AccessibleJComponent this$1) {
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
