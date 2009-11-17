package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JCheckBox$AccessibleJCheckBox extends JToggleButton$AccessibleJToggleButton {
    /*synthetic*/ final JCheckBox this$0;
    
    protected JCheckBox$AccessibleJCheckBox(/*synthetic*/ final JCheckBox this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.CHECK_BOX;
    }
}
