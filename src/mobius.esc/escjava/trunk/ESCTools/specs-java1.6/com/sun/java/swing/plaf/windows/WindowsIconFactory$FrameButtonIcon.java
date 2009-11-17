package com.sun.java.swing.plaf.windows;

import javax.swing.*;
import java.awt.*;
import java.io.Serializable;
import com.sun.java.swing.plaf.windows.TMSchema.*;
import com.sun.java.swing.plaf.windows.XPStyle.Skin;

class WindowsIconFactory$FrameButtonIcon implements Icon, Serializable {
    
    /*synthetic*/ WindowsIconFactory$FrameButtonIcon(Part x0, com.sun.java.swing.plaf.windows.WindowsIconFactory$1 x1) {
        this(x0);
    }
    private TMSchema$Part part;
    
    private WindowsIconFactory$FrameButtonIcon(TMSchema$Part part) {
        
        this.part = part;
    }
    
    public void paintIcon(Component c, Graphics g, int x0, int y0) {
        int width = getIconWidth();
        int height = getIconHeight();
        XPStyle xp = XPStyle.getXP();
        if (xp != null) {
            XPStyle$Skin skin = xp.getSkin(c, part);
            JButton b = (JButton)(JButton)c;
            ButtonModel model = b.getModel();
            JInternalFrame jif = (JInternalFrame)(JInternalFrame)SwingUtilities.getAncestorOfClass(JInternalFrame.class, b);
            boolean jifSelected = (jif != null && jif.isSelected());
            TMSchema$State state;
            if (jifSelected) {
                if (!model.isEnabled()) {
                    state = TMSchema$State.DISABLED;
                } else if (model.isArmed() && model.isPressed()) {
                    state = TMSchema$State.PUSHED;
                } else if (model.isRollover()) {
                    state = TMSchema$State.HOT;
                } else {
                    state = TMSchema$State.NORMAL;
                }
            } else {
                if (!model.isEnabled()) {
                    state = TMSchema$State.INACTIVEDISABLED;
                } else if (model.isArmed() && model.isPressed()) {
                    state = TMSchema$State.INACTIVEPUSHED;
                } else if (model.isRollover()) {
                    state = TMSchema$State.INACTIVEHOT;
                } else {
                    state = TMSchema$State.INACTIVENORMAL;
                }
            }
            skin.paintSkin(g, 0, 0, width, height, state);
        } else {
            g.setColor(Color.black);
            int x = width / 12 + 2;
            int y = height / 5;
            int h = height - y * 2 - 1;
            int w = width * 3 / 4 - 3;
            int thickness2 = Math.max(height / 8, 2);
            int thickness = Math.max(width / 15, 1);
            if (part == TMSchema$Part.WP_CLOSEBUTTON) {
                int lineWidth;
                if (width > 47) lineWidth = 6; else if (width > 37) lineWidth = 5; else if (width > 26) lineWidth = 4; else if (width > 16) lineWidth = 3; else if (width > 12) lineWidth = 2; else lineWidth = 1;
                y = height / 12 + 2;
                if (lineWidth == 1) {
                    if (w % 2 == 1) {
                        x++;
                        w++;
                    }
                    g.drawLine(x, y, x + w - 2, y + w - 2);
                    g.drawLine(x + w - 2, y, x, y + w - 2);
                } else if (lineWidth == 2) {
                    if (w > 6) {
                        x++;
                        w--;
                    }
                    g.drawLine(x, y, x + w - 2, y + w - 2);
                    g.drawLine(x + w - 2, y, x, y + w - 2);
                    g.drawLine(x + 1, y, x + w - 1, y + w - 2);
                    g.drawLine(x + w - 1, y, x + 1, y + w - 2);
                } else {
                    x += 2;
                    y++;
                    w -= 2;
                    g.drawLine(x, y, x + w - 1, y + w - 1);
                    g.drawLine(x + w - 1, y, x, y + w - 1);
                    g.drawLine(x + 1, y, x + w - 1, y + w - 2);
                    g.drawLine(x + w - 2, y, x, y + w - 2);
                    g.drawLine(x, y + 1, x + w - 2, y + w - 1);
                    g.drawLine(x + w - 1, y + 1, x + 1, y + w - 1);
                    for (int i = 4; i <= lineWidth; i++) {
                        g.drawLine(x + i - 2, y, x + w - 1, y + w - i + 1);
                        g.drawLine(x, y + i - 2, x + w - i + 1, y + w - 1);
                        g.drawLine(x + w - i + 1, y, x, y + w - i + 1);
                        g.drawLine(x + w - 1, y + i - 2, x + i - 2, y + w - 1);
                    }
                }
            } else if (part == TMSchema$Part.WP_MINBUTTON) {
                g.fillRect(x, y + h - thickness2, w - w / 3, thickness2);
            } else if (part == TMSchema$Part.WP_MAXBUTTON) {
                g.fillRect(x, y, w, thickness2);
                g.fillRect(x, y, thickness, h);
                g.fillRect(x + w - thickness, y, thickness, h);
                g.fillRect(x, y + h - thickness, w, thickness);
            } else if (part == TMSchema$Part.WP_RESTOREBUTTON) {
                g.fillRect(x + w / 3, y, w - w / 3, thickness2);
                g.fillRect(x + w / 3, y, thickness, h / 3);
                g.fillRect(x + w - thickness, y, thickness, h - h / 3);
                g.fillRect(x + w - w / 3, y + h - h / 3 - thickness, w / 3, thickness);
                g.fillRect(x, y + h / 3, w - w / 3, thickness2);
                g.fillRect(x, y + h / 3, thickness, h - h / 3);
                g.fillRect(x + w - w / 3 - thickness, y + h / 3, thickness, h - h / 3);
                g.fillRect(x, y + h - thickness, w - w / 3, thickness);
            }
        }
    }
    
    public int getIconWidth() {
        int width;
        if (XPStyle.getXP() != null) {
            width = UIManager.getInt("InternalFrame.titleButtonHeight") - 2;
        } else {
            width = UIManager.getInt("InternalFrame.titleButtonWidth") - 2;
        }
        if (XPStyle.getXP() != null) {
            width -= 2;
        }
        return width;
    }
    
    public int getIconHeight() {
        int height = UIManager.getInt("InternalFrame.titleButtonHeight") - 4;
        return height;
    }
}
