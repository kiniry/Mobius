package com.sun.java.swing.plaf.windows;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;
import com.sun.java.swing.plaf.windows.TMSchema.*;
import com.sun.java.swing.plaf.windows.XPStyle.Skin;

class WindowsIconFactory$MenuArrowIcon implements Icon, UIResource, Serializable {
    
    /*synthetic*/ WindowsIconFactory$MenuArrowIcon(com.sun.java.swing.plaf.windows.WindowsIconFactory$1 x0) {
        this();
    }
    
    private WindowsIconFactory$MenuArrowIcon() {
        
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        if (WindowsMenuItemUI.isVistaPainting()) {
            XPStyle xp = XPStyle.getXP();
            TMSchema$State state = TMSchema$State.NORMAL;
            if (c instanceof JMenuItem) {
                state = ((JMenuItem)(JMenuItem)c).getModel().isEnabled() ? TMSchema$State.NORMAL : TMSchema$State.DISABLED;
            }
            XPStyle$Skin skin = xp.getSkin(c, TMSchema$Part.MP_POPUPSUBMENU);
            if (WindowsGraphicsUtils.isLeftToRight(c)) {
                skin.paintSkin(g, x, y, state);
            } else {
                Graphics2D g2d = (Graphics2D)(Graphics2D)g.create();
                g2d.translate(x + skin.getWidth(), y);
                g2d.scale(-1, 1);
                skin.paintSkin(g2d, 0, 0, state);
                g2d.dispose();
            }
        } else {
            g.translate(x, y);
            if (WindowsGraphicsUtils.isLeftToRight(c)) {
                g.drawLine(0, 0, 0, 7);
                g.drawLine(1, 1, 1, 6);
                g.drawLine(2, 2, 2, 5);
                g.drawLine(3, 3, 3, 4);
            } else {
                g.drawLine(4, 0, 4, 7);
                g.drawLine(3, 1, 3, 6);
                g.drawLine(2, 2, 2, 5);
                g.drawLine(1, 3, 1, 4);
            }
            g.translate(-x, -y);
        }
    }
    
    public int getIconWidth() {
        if (WindowsMenuItemUI.isVistaPainting()) {
            XPStyle$Skin skin = XPStyle.getXP().getSkin(null, TMSchema$Part.MP_POPUPSUBMENU);
            return skin.getWidth();
        } else {
            return 4;
        }
    }
    
    public int getIconHeight() {
        if (WindowsMenuItemUI.isVistaPainting()) {
            XPStyle$Skin skin = XPStyle.getXP().getSkin(null, TMSchema$Part.MP_POPUPSUBMENU);
            return skin.getHeight();
        } else {
            return 8;
        }
    }
}
