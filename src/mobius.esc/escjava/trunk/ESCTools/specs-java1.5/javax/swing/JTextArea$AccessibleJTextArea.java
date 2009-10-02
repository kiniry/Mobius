package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.swing.text.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JTextArea$AccessibleJTextArea extends JTextComponent$AccessibleJTextComponent {
    /*synthetic*/ final JTextArea this$0;
    
    protected JTextArea$AccessibleJTextArea(/*synthetic*/ final JTextArea this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        states.add(AccessibleState.MULTI_LINE);
        return states;
    }
}
