package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JInternalFrame$AccessibleJInternalFrame extends JComponent$AccessibleJComponent implements AccessibleValue {
    /*synthetic*/ final JInternalFrame this$0;
    
    protected JInternalFrame$AccessibleJInternalFrame(/*synthetic*/ final JInternalFrame this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public String getAccessibleName() {
        if (accessibleName != null) {
            return accessibleName;
        } else {
            return this$0.getTitle();
        }
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.INTERNAL_FRAME;
    }
    
    public AccessibleValue getAccessibleValue() {
        return this;
    }
    
    public Number getCurrentAccessibleValue() {
        return new Integer(this$0.getLayer());
    }
    
    public boolean setCurrentAccessibleValue(Number n) {
        if (n == null) {
            return false;
        }
        this$0.setLayer(new Integer(n.intValue()));
        return true;
    }
    
    public Number getMinimumAccessibleValue() {
        return new Integer(Integer.MIN_VALUE);
    }
    
    public Number getMaximumAccessibleValue() {
        return new Integer(Integer.MAX_VALUE);
    }
}
