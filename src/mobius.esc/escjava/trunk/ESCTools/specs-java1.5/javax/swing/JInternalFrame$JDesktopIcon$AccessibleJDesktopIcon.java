package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JInternalFrame$JDesktopIcon$AccessibleJDesktopIcon extends JComponent$AccessibleJComponent implements AccessibleValue {
    /*synthetic*/ final JInternalFrame$JDesktopIcon this$0;
    
    protected JInternalFrame$JDesktopIcon$AccessibleJDesktopIcon(/*synthetic*/ final JInternalFrame$JDesktopIcon this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.DESKTOP_ICON;
    }
    
    public AccessibleValue getAccessibleValue() {
        return this;
    }
    
    public Number getCurrentAccessibleValue() {
        AccessibleContext a = this$0.getInternalFrame().getAccessibleContext();
        AccessibleValue v = a.getAccessibleValue();
        if (v != null) {
            return v.getCurrentAccessibleValue();
        } else {
            return null;
        }
    }
    
    public boolean setCurrentAccessibleValue(Number n) {
        if (n == null) {
            return false;
        }
        AccessibleContext a = this$0.getInternalFrame().getAccessibleContext();
        AccessibleValue v = a.getAccessibleValue();
        if (v != null) {
            return v.setCurrentAccessibleValue(n);
        } else {
            return false;
        }
    }
    
    public Number getMinimumAccessibleValue() {
        AccessibleContext a = this$0.getInternalFrame().getAccessibleContext();
        if (a instanceof AccessibleValue) {
            return ((AccessibleValue)(AccessibleValue)a).getMinimumAccessibleValue();
        } else {
            return null;
        }
    }
    
    public Number getMaximumAccessibleValue() {
        AccessibleContext a = this$0.getInternalFrame().getAccessibleContext();
        if (a instanceof AccessibleValue) {
            return ((AccessibleValue)(AccessibleValue)a).getMaximumAccessibleValue();
        } else {
            return null;
        }
    }
}
