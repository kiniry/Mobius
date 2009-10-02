package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JRadioButton$AccessibleJRadioButton extends JToggleButton$AccessibleJToggleButton {
    /*synthetic*/ final JRadioButton this$0;
    
    protected JRadioButton$AccessibleJRadioButton(/*synthetic*/ final JRadioButton this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.RADIO_BUTTON;
    }
}
