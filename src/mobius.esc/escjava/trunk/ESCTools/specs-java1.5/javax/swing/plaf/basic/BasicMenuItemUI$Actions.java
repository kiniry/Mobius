package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import sun.swing.UIAction;

class BasicMenuItemUI$Actions extends UIAction {
    private static final String CLICK = "doClick";
    
    BasicMenuItemUI$Actions(String key) {
        super(key);
    }
    
    public void actionPerformed(ActionEvent e) {
        JMenuItem mi = (JMenuItem)(JMenuItem)e.getSource();
        MenuSelectionManager.defaultManager().clearSelectedPath();
        mi.doClick();
    }
}
