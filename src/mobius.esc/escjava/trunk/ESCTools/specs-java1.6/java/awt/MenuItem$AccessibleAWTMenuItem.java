package java.awt;

import java.awt.event.*;
import javax.accessibility.*;

public class MenuItem$AccessibleAWTMenuItem extends MenuComponent$AccessibleAWTMenuComponent implements AccessibleAction, AccessibleValue {
    /*synthetic*/ final MenuItem this$0;
    
    protected MenuItem$AccessibleAWTMenuItem(/*synthetic*/ final MenuItem this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    private static final long serialVersionUID = -217847831945965825L;
    
    public String getAccessibleName() {
        if (accessibleName != null) {
            return accessibleName;
        } else {
            if (this$0.getLabel() == null) {
                return super.getAccessibleName();
            } else {
                return this$0.getLabel();
            }
        }
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.MENU_ITEM;
    }
    
    public AccessibleAction getAccessibleAction() {
        return this;
    }
    
    public AccessibleValue getAccessibleValue() {
        return this;
    }
    
    public int getAccessibleActionCount() {
        return 1;
    }
    
    public String getAccessibleActionDescription(int i) {
        if (i == 0) {
            return new String("click");
        } else {
            return null;
        }
    }
    
    public boolean doAccessibleAction(int i) {
        if (i == 0) {
            Toolkit.getEventQueue().postEvent(new ActionEvent(this$0, ActionEvent.ACTION_PERFORMED, this$0.getActionCommand(), EventQueue.getMostRecentEventTime(), 0));
            return true;
        } else {
            return false;
        }
    }
    
    public Number getCurrentAccessibleValue() {
        return new Integer(0);
    }
    
    public boolean setCurrentAccessibleValue(Number n) {
        return false;
    }
    
    public Number getMinimumAccessibleValue() {
        return new Integer(0);
    }
    
    public Number getMaximumAccessibleValue() {
        return new Integer(0);
    }
}
