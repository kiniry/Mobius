package java.awt;

import java.awt.event.*;
import javax.accessibility.*;

public class Frame$AccessibleAWTFrame extends Window$AccessibleAWTWindow {
    /*synthetic*/ final Frame this$0;
    
    protected Frame$AccessibleAWTFrame(/*synthetic*/ final Frame this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    private static final long serialVersionUID = -6172960752956030250L;
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.FRAME;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        if (this$0.getFocusOwner() != null) {
            states.add(AccessibleState.ACTIVE);
        }
        if (this$0.isResizable()) {
            states.add(AccessibleState.RESIZABLE);
        }
        return states;
    }
}
