package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.text.*;
import javax.swing.plaf.*;
import javax.swing.event.*;
import javax.accessibility.*;

public class JTextField$AccessibleJTextField extends JTextComponent$AccessibleJTextComponent {
    /*synthetic*/ final JTextField this$0;
    
    protected JTextField$AccessibleJTextField(/*synthetic*/ final JTextField this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        states.add(AccessibleState.SINGLE_LINE);
        return states;
    }
}
