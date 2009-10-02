package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import javax.swing.plaf.*;
import javax.swing.event.*;
import javax.accessibility.*;

public class JButton$AccessibleJButton extends AbstractButton$AccessibleAbstractButton {
    /*synthetic*/ final JButton this$0;
    
    protected JButton$AccessibleJButton(/*synthetic*/ final JButton this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.PUSH_BUTTON;
    }
}
