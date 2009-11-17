package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.swing.event.*;
import javax.swing.border.*;
import javax.accessibility.*;

public class JViewport$AccessibleJViewport extends JComponent$AccessibleJComponent {
    /*synthetic*/ final JViewport this$0;
    
    protected JViewport$AccessibleJViewport(/*synthetic*/ final JViewport this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.VIEWPORT;
    }
}
