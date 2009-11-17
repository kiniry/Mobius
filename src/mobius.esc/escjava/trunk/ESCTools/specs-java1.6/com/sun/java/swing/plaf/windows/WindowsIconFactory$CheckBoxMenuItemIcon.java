package com.sun.java.swing.plaf.windows;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class WindowsIconFactory$CheckBoxMenuItemIcon implements Icon, UIResource, Serializable {
    
    /*synthetic*/ WindowsIconFactory$CheckBoxMenuItemIcon(com.sun.java.swing.plaf.windows.WindowsIconFactory$1 x0) {
        this();
    }
    
    private WindowsIconFactory$CheckBoxMenuItemIcon() {
        
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        AbstractButton b = (AbstractButton)(AbstractButton)c;
        ButtonModel model = b.getModel();
        boolean isSelected = model.isSelected();
        if (isSelected) {
            y = y - getIconHeight() / 2;
            g.drawLine(x + 9, y + 3, x + 9, y + 3);
            g.drawLine(x + 8, y + 4, x + 9, y + 4);
            g.drawLine(x + 7, y + 5, x + 9, y + 5);
            g.drawLine(x + 6, y + 6, x + 8, y + 6);
            g.drawLine(x + 3, y + 7, x + 7, y + 7);
            g.drawLine(x + 4, y + 8, x + 6, y + 8);
            g.drawLine(x + 5, y + 9, x + 5, y + 9);
            g.drawLine(x + 3, y + 5, x + 3, y + 5);
            g.drawLine(x + 3, y + 6, x + 4, y + 6);
        }
    }
    
    public int getIconWidth() {
        return 9;
    }
    
    public int getIconHeight() {
        return 9;
    }
}
