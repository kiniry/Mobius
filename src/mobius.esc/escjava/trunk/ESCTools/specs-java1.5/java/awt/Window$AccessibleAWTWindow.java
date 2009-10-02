package java.awt;

import java.awt.event.*;
import javax.accessibility.*;

public class Window$AccessibleAWTWindow extends Container$AccessibleAWTContainer {
    /*synthetic*/ final Window this$0;
    
    protected Window$AccessibleAWTWindow(/*synthetic*/ final Window this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    private static final long serialVersionUID = 4215068635060671780L;
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.WINDOW;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        if (this$0.getFocusOwner() != null) {
            states.add(AccessibleState.ACTIVE);
        }
        return states;
    }
}
