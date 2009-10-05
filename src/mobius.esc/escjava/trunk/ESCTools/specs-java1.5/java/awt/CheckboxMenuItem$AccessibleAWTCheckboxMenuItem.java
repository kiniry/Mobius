package java.awt;

import java.awt.event.*;
import javax.accessibility.*;

public class CheckboxMenuItem$AccessibleAWTCheckboxMenuItem extends MenuItem$AccessibleAWTMenuItem implements AccessibleAction, AccessibleValue {
    /*synthetic*/ final CheckboxMenuItem this$0;
    
    protected CheckboxMenuItem$AccessibleAWTCheckboxMenuItem(/*synthetic*/ final CheckboxMenuItem this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    private static final long serialVersionUID = -1122642964303476L;
    
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
}
