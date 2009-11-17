package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.text.*;
import java.awt.geom.*;
import java.beans.*;
import java.io.Serializable;
import javax.swing.event.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import javax.swing.text.*;
import javax.swing.text.html.*;
import javax.swing.plaf.basic.*;
import java.util.*;

class AbstractButton$ButtonActionPropertyChangeListener extends AbstractActionPropertyChangeListener implements Serializable {
    
    AbstractButton$ButtonActionPropertyChangeListener(AbstractButton b, Action a) {
        super(b, a);
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String propertyName = e.getPropertyName();
        AbstractButton button = (AbstractButton)(AbstractButton)getTarget();
        if (button == null) {
            Action action = (Action)(Action)e.getSource();
            action.removePropertyChangeListener(this);
        } else {
            if (e.getPropertyName().equals(Action.NAME)) {
                Boolean hide = (Boolean)(Boolean)button.getClientProperty("hideActionText");
                if (hide == null || hide == Boolean.FALSE) {
                    String text = (String)(String)e.getNewValue();
                    button.setText(text);
                    button.repaint();
                }
            } else if (e.getPropertyName().equals(Action.SHORT_DESCRIPTION)) {
                String text = (String)(String)e.getNewValue();
                button.setToolTipText(text);
            } else if (propertyName.equals("enabled")) {
                Boolean enabledState = (Boolean)(Boolean)e.getNewValue();
                button.setEnabled(enabledState.booleanValue());
                button.repaint();
            } else if (e.getPropertyName().equals(Action.SMALL_ICON)) {
                Icon icon = (Icon)(Icon)e.getNewValue();
                button.setIcon(icon);
                button.invalidate();
                button.repaint();
            } else if (e.getPropertyName().equals(Action.MNEMONIC_KEY)) {
                Integer mn = (Integer)(Integer)e.getNewValue();
                button.setMnemonic(mn.intValue());
                button.invalidate();
                button.repaint();
            } else if (e.getPropertyName().equals(Action.ACTION_COMMAND_KEY)) {
                button.setActionCommand((String)(String)e.getNewValue());
            }
        }
    }
}
