package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.text.*;
import javax.swing.plaf.*;
import javax.swing.event.*;
import javax.accessibility.*;

class JTextField$NotifyAction extends TextAction {
    
    JTextField$NotifyAction() {
        super("notify-field-accept");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getFocusedComponent();
        if (target instanceof JTextField) {
            JTextField field = (JTextField)(JTextField)target;
            field.postActionEvent();
        }
    }
    
    public boolean isEnabled() {
        JTextComponent target = getFocusedComponent();
        if (target instanceof JTextField) {
            return ((JTextField)(JTextField)target).hasActionListener();
        }
        return false;
    }
}
