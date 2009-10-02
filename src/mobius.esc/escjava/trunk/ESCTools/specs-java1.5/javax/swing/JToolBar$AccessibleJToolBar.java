package javax.swing;

import java.awt.event.*;
import java.beans.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JToolBar$AccessibleJToolBar extends JComponent$AccessibleJComponent {
    /*synthetic*/ final JToolBar this$0;
    
    protected JToolBar$AccessibleJToolBar(/*synthetic*/ final JToolBar this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        return states;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.TOOL_BAR;
    }
}
