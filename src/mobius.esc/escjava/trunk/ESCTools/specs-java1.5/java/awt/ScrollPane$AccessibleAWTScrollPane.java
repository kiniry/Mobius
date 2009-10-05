package java.awt;

import java.awt.event.*;
import javax.accessibility.*;

public class ScrollPane$AccessibleAWTScrollPane extends Container$AccessibleAWTContainer {
    /*synthetic*/ final ScrollPane this$0;
    
    protected ScrollPane$AccessibleAWTScrollPane(/*synthetic*/ final ScrollPane this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    private static final long serialVersionUID = 6100703663886637L;
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.SCROLL_PANE;
    }
}
