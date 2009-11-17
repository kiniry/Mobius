package javax.swing;

import javax.swing.text.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JPasswordField$AccessibleJPasswordField extends JTextField$AccessibleJTextField {
    /*synthetic*/ final JPasswordField this$0;
    
    protected JPasswordField$AccessibleJPasswordField(/*synthetic*/ final JPasswordField this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.PASSWORD_TEXT;
    }
}
