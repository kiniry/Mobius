package javax.swing;

import javax.accessibility.*;

public class JOptionPane$AccessibleJOptionPane extends JComponent$AccessibleJComponent {
    /*synthetic*/ final JOptionPane this$0;
    
    protected JOptionPane$AccessibleJOptionPane(/*synthetic*/ final JOptionPane this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.OPTION_PANE;
    }
}
