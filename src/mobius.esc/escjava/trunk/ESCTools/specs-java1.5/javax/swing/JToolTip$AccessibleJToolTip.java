package javax.swing;

import javax.swing.plaf.*;
import javax.accessibility.*;

public class JToolTip$AccessibleJToolTip extends JComponent$AccessibleJComponent {
    /*synthetic*/ final JToolTip this$0;
    
    protected JToolTip$AccessibleJToolTip(/*synthetic*/ final JToolTip this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public String getAccessibleDescription() {
        if (accessibleDescription != null) {
            return accessibleDescription;
        } else {
            return this$0.getTipText();
        }
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.TOOL_TIP;
    }
}
