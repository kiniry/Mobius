package java.applet;

import java.awt.*;
import javax.accessibility.*;

public class Applet$AccessibleApplet extends Panel$AccessibleAWTPanel {
    /*synthetic*/ final Applet this$0;
    
    protected Applet$AccessibleApplet(/*synthetic*/ final Applet this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    private static final long serialVersionUID = 8127374778187708896L;
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.FRAME;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        states.add(AccessibleState.ACTIVE);
        return states;
    }
}
