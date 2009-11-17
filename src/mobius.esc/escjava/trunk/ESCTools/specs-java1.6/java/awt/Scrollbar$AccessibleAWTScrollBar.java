package java.awt;

import java.awt.event.*;
import javax.accessibility.*;

public class Scrollbar$AccessibleAWTScrollBar extends Component$AccessibleAWTComponent implements AccessibleValue {
    /*synthetic*/ final Scrollbar this$0;
    
    protected Scrollbar$AccessibleAWTScrollBar(/*synthetic*/ final Scrollbar this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    private static final long serialVersionUID = -344337268523697807L;
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        if (this$0.getValueIsAdjusting()) {
            states.add(AccessibleState.BUSY);
        }
        if (this$0.getOrientation() == 1) {
            states.add(AccessibleState.VERTICAL);
        } else {
            states.add(AccessibleState.HORIZONTAL);
        }
        return states;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.SCROLL_BAR;
    }
    
    public AccessibleValue getAccessibleValue() {
        return this;
    }
    
    public Number getCurrentAccessibleValue() {
        return new Integer(this$0.getValue());
    }
    
    public boolean setCurrentAccessibleValue(Number n) {
        if (n instanceof Integer) {
            this$0.setValue(n.intValue());
            return true;
        } else {
            return false;
        }
    }
    
    public Number getMinimumAccessibleValue() {
        return new Integer(this$0.getMinimum());
    }
    
    public Number getMaximumAccessibleValue() {
        return new Integer(this$0.getMaximum());
    }
}
