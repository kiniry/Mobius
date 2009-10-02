package javax.swing;

import java.awt.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JPanel$AccessibleJPanel extends JComponent$AccessibleJComponent {
    /*synthetic*/ final JPanel this$0;
    
    protected JPanel$AccessibleJPanel(/*synthetic*/ final JPanel this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.PANEL;
    }
}
