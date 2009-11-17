package javax.swing.plaf.basic;

import sun.swing.UIAction;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.*;
import javax.swing.event.*;

class BasicButtonListener$Actions extends UIAction {
    private static final String PRESS = "pressed";
    private static final String RELEASE = "released";
    
    BasicButtonListener$Actions(String name) {
        super(name);
    }
    
    public void actionPerformed(ActionEvent e) {
        AbstractButton b = (AbstractButton)(AbstractButton)e.getSource();
        String key = getName();
        if (key == PRESS) {
            ButtonModel model = b.getModel();
            model.setArmed(true);
            model.setPressed(true);
            if (!b.hasFocus()) {
                b.requestFocus();
            }
        } else if (key == RELEASE) {
            ButtonModel model = b.getModel();
            model.setPressed(false);
            model.setArmed(false);
        }
    }
    
    public boolean isEnabled(Object sender) {
        if (sender != null && (sender instanceof AbstractButton) && !((AbstractButton)(AbstractButton)sender).getModel().isEnabled()) {
            return false;
        } else {
            return true;
        }
    }
}
