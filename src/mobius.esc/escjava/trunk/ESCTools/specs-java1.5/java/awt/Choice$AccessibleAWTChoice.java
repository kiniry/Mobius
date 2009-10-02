package java.awt;

import java.util.*;
import java.awt.event.*;
import javax.accessibility.*;

public class Choice$AccessibleAWTChoice extends Component$AccessibleAWTComponent implements AccessibleAction {
    /*synthetic*/ final Choice this$0;
    private static final long serialVersionUID = 7175603582428509322L;
    
    public Choice$AccessibleAWTChoice(/*synthetic*/ final Choice this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    
    public AccessibleAction getAccessibleAction() {
        return this;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.COMBO_BOX;
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
}
