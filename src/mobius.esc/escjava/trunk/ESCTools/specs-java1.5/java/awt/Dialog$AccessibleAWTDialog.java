package java.awt;

import java.awt.event.*;
import javax.accessibility.*;

public class Dialog$AccessibleAWTDialog extends Window$AccessibleAWTWindow {
    /*synthetic*/ final Dialog this$0;
    
    protected Dialog$AccessibleAWTDialog(/*synthetic*/ final Dialog this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    private static final long serialVersionUID = 4837230331833941201L;
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.DIALOG;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        if (this$0.getFocusOwner() != null) {
            states.add(AccessibleState.ACTIVE);
        }
        if (this$0.isModal()) {
            states.add(AccessibleState.MODAL);
        }
        if (this$0.isResizable()) {
            states.add(AccessibleState.RESIZABLE);
        }
        return states;
    }
}
