package javax.swing;

import javax.swing.plaf.*;
import javax.accessibility.*;

public class JDesktopPane$AccessibleJDesktopPane extends JComponent$AccessibleJComponent {
    /*synthetic*/ final JDesktopPane this$0;
    
    protected JDesktopPane$AccessibleJDesktopPane(/*synthetic*/ final JDesktopPane this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.DESKTOP_PANE;
    }
}
