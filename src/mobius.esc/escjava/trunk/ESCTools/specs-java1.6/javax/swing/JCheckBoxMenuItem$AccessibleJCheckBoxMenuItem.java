package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JCheckBoxMenuItem$AccessibleJCheckBoxMenuItem extends JMenuItem$AccessibleJMenuItem {
    /*synthetic*/ final JCheckBoxMenuItem this$0;
    
    protected JCheckBoxMenuItem$AccessibleJCheckBoxMenuItem(/*synthetic*/ final JCheckBoxMenuItem this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.CHECK_BOX;
    }
}
