package java.awt;

import java.awt.event.*;
import javax.accessibility.*;

public class Checkbox$AccessibleAWTCheckbox extends Component$AccessibleAWTComponent implements ItemListener, AccessibleAction, AccessibleValue {
    /*synthetic*/ final Checkbox this$0;
    private static final long serialVersionUID = 7881579233144754107L;
    
    public Checkbox$AccessibleAWTCheckbox(/*synthetic*/ final Checkbox this$0) {
        this.this$0 = this$0;
        super(this$0);
        this$0.addItemListener(this);
    }
    
    public void itemStateChanged(ItemEvent e) {
        Checkbox cb = (Checkbox)(Checkbox)e.getSource();
        if (this$0.accessibleContext != null) {
            if (cb.getState()) {
                this$0.accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.CHECKED);
            } else {
                this$0.accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.CHECKED, null);
            }
        }
    }
    
    public AccessibleAction getAccessibleAction() {
        return this;
    }
    
    public AccessibleValue getAccessibleValue() {
        return this;
    }
    
    public int getAccessibleActionCount() {
        return 0;
    }
    
    public String getAccessibleActionDescription(int i) {
        return null;
    }
    
    public boolean doAccessibleAction(int i) {
        return false;
    }
    
    public Number getCurrentAccessibleValue() {
        return null;
    }
    
    public boolean setCurrentAccessibleValue(Number n) {
        return false;
    }
    
    public Number getMinimumAccessibleValue() {
        return null;
    }
    
    public Number getMaximumAccessibleValue() {
        return null;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.CHECK_BOX;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        if (this$0.getState()) {
            states.add(AccessibleState.CHECKED);
        }
        return states;
    }
}
