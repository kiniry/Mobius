package javax.swing;

import javax.swing.plaf.*;
import javax.accessibility.*;
import java.awt.*;

public class JSplitPane$AccessibleJSplitPane extends JComponent$AccessibleJComponent implements AccessibleValue {
    /*synthetic*/ final JSplitPane this$0;
    
    protected JSplitPane$AccessibleJSplitPane(/*synthetic*/ final JSplitPane this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        if (this$0.getOrientation() == 0) {
            states.add(AccessibleState.VERTICAL);
        } else {
            states.add(AccessibleState.HORIZONTAL);
        }
        return states;
    }
    
    public AccessibleValue getAccessibleValue() {
        return this;
    }
    
    public Number getCurrentAccessibleValue() {
        return new Integer(this$0.getDividerLocation());
    }
    
    public boolean setCurrentAccessibleValue(Number n) {
        if (n == null) {
            return false;
        }
        this$0.setDividerLocation(n.intValue());
        return true;
    }
    
    public Number getMinimumAccessibleValue() {
        return new Integer(this$0.getUI().getMinimumDividerLocation(this$0));
    }
    
    public Number getMaximumAccessibleValue() {
        return new Integer(this$0.getUI().getMaximumDividerLocation(this$0));
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.SPLIT_PANE;
    }
}
