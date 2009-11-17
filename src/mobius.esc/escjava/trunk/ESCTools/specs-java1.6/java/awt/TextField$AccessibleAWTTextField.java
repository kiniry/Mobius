package java.awt;

import java.awt.event.*;
import javax.accessibility.*;

public class TextField$AccessibleAWTTextField extends TextComponent$AccessibleAWTTextComponent {
    /*synthetic*/ final TextField this$0;
    
    protected TextField$AccessibleAWTTextField(/*synthetic*/ final TextField this$0) {
        super(this$0);
        this.this$0 = this$0;

    }
    private static final long serialVersionUID = 6219164359235943158L;
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        states.add(AccessibleState.SINGLE_LINE);
        return states;
    }
}
