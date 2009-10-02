package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JCheckBox$1 extends AbstractActionPropertyChangeListener {
    /*synthetic*/ final JCheckBox this$0;
    
    JCheckBox$1(/*synthetic*/ final JCheckBox this$0, .javax.swing.JComponent x0, .javax.swing.Action x1) {
        this.this$0 = this$0;
        super(x0, x1);
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String propertyName = e.getPropertyName();
        AbstractButton button = (AbstractButton)(AbstractButton)getTarget();
        if (button == null) {
            Action action = (Action)(Action)e.getSource();
            action.removePropertyChangeListener(this);
        } else {
            if (propertyName.equals(Action.NAME)) {
                String text = (String)(String)e.getNewValue();
                button.setText(text);
                button.repaint();
            } else if (propertyName.equals(Action.SHORT_DESCRIPTION)) {
                String text = (String)(String)e.getNewValue();
                button.setToolTipText(text);
            } else if (propertyName.equals("enabled")) {
                Boolean enabledState = (Boolean)(Boolean)e.getNewValue();
                button.setEnabled(enabledState.booleanValue());
                button.repaint();
            } else if (propertyName.equals(Action.ACTION_COMMAND_KEY)) {
                button.setActionCommand((String)(String)e.getNewValue());
            }
        }
    }
}
