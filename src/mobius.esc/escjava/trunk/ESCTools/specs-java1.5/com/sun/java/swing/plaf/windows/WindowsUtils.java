package com.sun.java.swing.plaf.windows;

import javax.swing.plaf.*;
import javax.swing.*;
import java.awt.*;

class WindowsUtils {
    
    WindowsUtils() {
        
    }
    
    static boolean isLeftToRight(Component c) {
        return c.getComponentOrientation().isLeftToRight();
    }
    
    static void repaintMnemonicsInWindow(Window w) {
        if (w == null || !w.isShowing()) {
            return;
        }
        Window[] ownedWindows = w.getOwnedWindows();
        for (int i = 0; i < ownedWindows.length; i++) {
            repaintMnemonicsInWindow(ownedWindows[i]);
        }
        repaintMnemonicsInContainer(w);
    }
    
    static void repaintMnemonicsInContainer(Container cont) {
        Component c;
        for (int i = 0; i < cont.getComponentCount(); i++) {
            c = cont.getComponent(i);
            if (c == null || !c.isVisible()) {
                continue;
            }
            if (c instanceof AbstractButton && ((AbstractButton)(AbstractButton)c).getMnemonic() != '\000') {
                c.repaint();
                continue;
            } else if (c instanceof JLabel && ((JLabel)(JLabel)c).getDisplayedMnemonic() != '\000') {
                c.repaint();
                continue;
            }
            if (c instanceof Container) {
                repaintMnemonicsInContainer((Container)(Container)c);
            }
        }
    }
}
