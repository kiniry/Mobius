package com.sun.java.swing.plaf.windows;

import javax.swing.*;
import java.awt.*;
import java.io.Serializable;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class WindowsIconFactory$ResizeIcon implements Icon, Serializable {
    
    /*synthetic*/ WindowsIconFactory$ResizeIcon(com.sun.java.swing.plaf.windows.WindowsIconFactory$1 x0) {
        this();
    }
    
    private WindowsIconFactory$ResizeIcon() {
        
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        g.setColor(UIManager.getColor("InternalFrame.resizeIconHighlight"));
        g.drawLine(0, 11, 11, 0);
        g.drawLine(4, 11, 11, 4);
        g.drawLine(8, 11, 11, 8);
        g.setColor(UIManager.getColor("InternalFrame.resizeIconShadow"));
        g.drawLine(1, 11, 11, 1);
        g.drawLine(2, 11, 11, 2);
        g.drawLine(5, 11, 11, 5);
        g.drawLine(6, 11, 11, 6);
        g.drawLine(9, 11, 11, 9);
        g.drawLine(10, 11, 11, 10);
    }
    
    public int getIconWidth() {
        return 13;
    }
    
    public int getIconHeight() {
        return 13;
    }
}
