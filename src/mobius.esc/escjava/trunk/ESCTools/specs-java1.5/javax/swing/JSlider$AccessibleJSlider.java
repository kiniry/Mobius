package javax.swing;

import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.util.*;
import java.beans.*;

public class JSlider$AccessibleJSlider extends JComponent$AccessibleJComponent implements AccessibleValue {
    /*synthetic*/ final JSlider this$0;
    
    protected JSlider$AccessibleJSlider(/*synthetic*/ final JSlider this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    
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
        return AccessibleRole.SLIDER;
    }
    
    public AccessibleValue getAccessibleValue() {
        return this;
    }
    
    public Number getCurrentAccessibleValue() {
        return new Integer(this$0.getValue());
    }
    
    public boolean setCurrentAccessibleValue(Number n) {
        if (n == null) {
            return false;
        }
        this$0.setValue(n.intValue());
        return true;
    }
    
    public Number getMinimumAccessibleValue() {
        return new Integer(this$0.getMinimum());
    }
    
    public Number getMaximumAccessibleValue() {
        BoundedRangeModel model = this$0.getModel();
        return new Integer(model.getMaximum() - model.getExtent());
    }
}
