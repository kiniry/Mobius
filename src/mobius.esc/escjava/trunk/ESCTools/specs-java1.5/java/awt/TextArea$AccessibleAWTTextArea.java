package java.awt;

import javax.accessibility.*;

public class TextArea$AccessibleAWTTextArea extends TextComponent$AccessibleAWTTextComponent {
    /*synthetic*/ final TextArea this$0;
    
    protected TextArea$AccessibleAWTTextArea(/*synthetic*/ final TextArea this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    private static final long serialVersionUID = 3472827823632144419L;
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        states.add(AccessibleState.MULTI_LINE);
        return states;
    }
}
