package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.accessibility.*;

public class JFrame$AccessibleJFrame extends Frame$AccessibleAWTFrame {
    /*synthetic*/ final JFrame this$0;
    
    protected JFrame$AccessibleJFrame(/*synthetic*/ final JFrame this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public String getAccessibleName() {
        if (accessibleName != null) {
            return accessibleName;
        } else {
            if (this$0.getTitle() == null) {
                return super.getAccessibleName();
            } else {
                return this$0.getTitle();
            }
        }
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        if (this$0.isResizable()) {
            states.add(AccessibleState.RESIZABLE);
        }
        if (this$0.getFocusOwner() != null) {
            states.add(AccessibleState.ACTIVE);
        }
        return states;
    }
}
