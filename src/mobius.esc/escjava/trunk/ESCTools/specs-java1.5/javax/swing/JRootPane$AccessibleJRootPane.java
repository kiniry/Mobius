package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.accessibility.*;
import javax.swing.border.*;

public class JRootPane$AccessibleJRootPane extends JComponent$AccessibleJComponent {
    /*synthetic*/ final JRootPane this$0;
    
    protected JRootPane$AccessibleJRootPane(/*synthetic*/ final JRootPane this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.ROOT_PANE;
    }
    
    public int getAccessibleChildrenCount() {
        return super.getAccessibleChildrenCount();
    }
    
    public Accessible getAccessibleChild(int i) {
        return super.getAccessibleChild(i);
    }
}
