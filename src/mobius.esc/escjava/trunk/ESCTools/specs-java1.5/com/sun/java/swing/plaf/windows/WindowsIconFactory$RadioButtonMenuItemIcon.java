package com.sun.java.swing.plaf.windows;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class WindowsIconFactory$RadioButtonMenuItemIcon implements Icon, UIResource, Serializable {
    
    /*synthetic*/ WindowsIconFactory$RadioButtonMenuItemIcon(com.sun.java.swing.plaf.windows.WindowsIconFactory$1 x0) {
        this();
    }
    
    private WindowsIconFactory$RadioButtonMenuItemIcon() {
        
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        AbstractButton b = (AbstractButton)(AbstractButton)c;
        ButtonModel model = b.getModel();
        if (b.isSelected() == true) {
            g.fillArc(0, 0, getIconWidth() - 2, getIconHeight() - 2, 0, 360);
        }
    }
    
    public int getIconWidth() {
        return 12;
    }
    
    public int getIconHeight() {
        return 12;
    }
}
