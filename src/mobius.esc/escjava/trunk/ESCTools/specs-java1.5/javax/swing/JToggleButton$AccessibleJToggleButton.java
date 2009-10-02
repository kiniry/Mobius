package javax.swing;

import java.awt.*;
import java.awt.event.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JToggleButton$AccessibleJToggleButton extends AbstractButton$AccessibleAbstractButton implements ItemListener {
    /*synthetic*/ final JToggleButton this$0;
    
    public JToggleButton$AccessibleJToggleButton(/*synthetic*/ final JToggleButton this$0) {
        this.this$0 = this$0;
        super(this$0);
        this$0.addItemListener(this);
    }
    
    public void itemStateChanged(ItemEvent e) {
        JToggleButton tb = (JToggleButton)(JToggleButton)e.getSource();
        if (this$0.accessibleContext != null) {
            if (tb.isSelected()) {
                this$0.accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.CHECKED);
            } else {
                this$0.accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.CHECKED, null);
            }
        }
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.TOGGLE_BUTTON;
    }
}
