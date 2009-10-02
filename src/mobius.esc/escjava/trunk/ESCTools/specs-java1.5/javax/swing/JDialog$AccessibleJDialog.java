package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.accessibility.*;

public class JDialog$AccessibleJDialog extends Dialog$AccessibleAWTDialog {
    /*synthetic*/ final JDialog this$0;
    
    protected JDialog$AccessibleJDialog(/*synthetic*/ final JDialog this$0) {
        this.this$0 = this$0;
        super(this$0);
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
        if (this$0.isModal()) {
            states.add(AccessibleState.MODAL);
        }
        return states;
    }
}
