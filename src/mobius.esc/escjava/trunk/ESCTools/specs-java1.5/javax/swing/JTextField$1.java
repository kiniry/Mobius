package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.text.*;
import javax.swing.plaf.*;
import javax.swing.event.*;
import javax.accessibility.*;

class JTextField$1 extends AbstractActionPropertyChangeListener {
    /*synthetic*/ final JTextField this$0;
    
    JTextField$1(/*synthetic*/ final JTextField this$0, .javax.swing.JComponent x0, .javax.swing.Action x1) {
        this.this$0 = this$0;
        super(x0, x1);
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String propertyName = e.getPropertyName();
        JTextField textField = (JTextField)(JTextField)getTarget();
        if (textField == null) {
            Action action = (Action)(Action)e.getSource();
            action.removePropertyChangeListener(this);
        } else {
            if (e.getPropertyName().equals(Action.SHORT_DESCRIPTION)) {
                String text = (String)(String)e.getNewValue();
                textField.setToolTipText(text);
            } else if (propertyName.equals("enabled")) {
                Boolean enabledState = (Boolean)(Boolean)e.getNewValue();
                textField.setEnabled(enabledState.booleanValue());
                textField.repaint();
            }
        }
    }
}
