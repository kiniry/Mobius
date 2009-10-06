package javax.swing;

import javax.accessibility.*;

public class JLayeredPane$AccessibleJLayeredPane extends JComponent$AccessibleJComponent {
    /*synthetic*/ final JLayeredPane this$0;
    
    protected JLayeredPane$AccessibleJLayeredPane(/*synthetic*/ final JLayeredPane this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.LAYERED_PANE;
    }
}
