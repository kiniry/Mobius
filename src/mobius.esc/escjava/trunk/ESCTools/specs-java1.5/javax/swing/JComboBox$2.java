package javax.swing;

import java.beans.*;
import java.util.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.accessibility.*;

class JComboBox$2 extends AbstractActionPropertyChangeListener {
    /*synthetic*/ final JComboBox this$0;
    
    JComboBox$2(/*synthetic*/ final JComboBox this$0, .javax.swing.JComponent x0, .javax.swing.Action x1) {
        this.this$0 = this$0;
        super(x0, x1);
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String propertyName = e.getPropertyName();
        JComboBox comboBox = (JComboBox)(JComboBox)getTarget();
        if (comboBox == null) {
            Action action = (Action)(Action)e.getSource();
            action.removePropertyChangeListener(this);
        } else {
            if (e.getPropertyName().equals(Action.SHORT_DESCRIPTION)) {
                String text = (String)(String)e.getNewValue();
                comboBox.setToolTipText(text);
            } else if (propertyName.equals("enabled")) {
                Boolean enabledState = (Boolean)(Boolean)e.getNewValue();
                comboBox.setEnabled(enabledState.booleanValue());
                comboBox.repaint();
            }
        }
    }
}
