package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.beans.PropertyChangeEvent;
import java.io.Serializable;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.swing.event.*;
import javax.accessibility.*;

class JMenuItem$MenuItemPropertyChangeListener extends AbstractActionPropertyChangeListener implements Serializable {
    
    JMenuItem$MenuItemPropertyChangeListener(JMenuItem m, Action a) {
        super(m, a);
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String propertyName = e.getPropertyName();
        JMenuItem mi = (JMenuItem)(JMenuItem)getTarget();
        if (mi == null) {
            Action action = (Action)(Action)e.getSource();
            action.removePropertyChangeListener(this);
        } else {
            if (e.getPropertyName().equals(Action.NAME)) {
                String text = (String)(String)e.getNewValue();
                mi.setText(text);
                mi.repaint();
            } else if (propertyName.equals("enabled")) {
                Boolean enabledState = (Boolean)(Boolean)e.getNewValue();
                mi.setEnabled(enabledState.booleanValue());
                mi.repaint();
            } else if (e.getPropertyName().equals(Action.SMALL_ICON)) {
                Icon icon = (Icon)(Icon)e.getNewValue();
                mi.setIcon(icon);
                mi.invalidate();
                mi.repaint();
            } else if (e.getPropertyName().equals(Action.MNEMONIC_KEY)) {
                Integer mn = (Integer)(Integer)e.getNewValue();
                mi.setMnemonic(mn.intValue());
                mi.invalidate();
                mi.repaint();
            }
        }
    }
}
