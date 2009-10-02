package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JRadioButtonMenuItem$AccessibleJRadioButtonMenuItem extends JMenuItem$AccessibleJMenuItem {
    /*synthetic*/ final JRadioButtonMenuItem this$0;
    
    protected JRadioButtonMenuItem$AccessibleJRadioButtonMenuItem(/*synthetic*/ final JRadioButtonMenuItem this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.RADIO_BUTTON;
    }
}
