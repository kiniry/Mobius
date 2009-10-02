package com.sun.java.swing.plaf.windows;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;
import com.sun.java.swing.plaf.windows.TMSchema.*;
import com.sun.java.swing.plaf.windows.XPStyle.Skin;

class WindowsIconFactory$RadioButtonIcon implements Icon, UIResource, Serializable {
    
    /*synthetic*/ WindowsIconFactory$RadioButtonIcon(com.sun.java.swing.plaf.windows.WindowsIconFactory$1 x0) {
        this();
    }
    
    private WindowsIconFactory$RadioButtonIcon() {
        
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        AbstractButton b = (AbstractButton)(AbstractButton)c;
        ButtonModel model = b.getModel();
        XPStyle xp = XPStyle.getXP();
        if (xp != null) {
            TMSchema$Part part = TMSchema$Part.BP_RADIOBUTTON;
            XPStyle$Skin skin = xp.getSkin(b, part);
            TMSchema$State state;
            int index = 0;
            if (model.isSelected()) {
                state = TMSchema$State.CHECKEDNORMAL;
                if (!model.isEnabled()) {
                    state = TMSchema$State.CHECKEDDISABLED;
                } else if (model.isPressed() && model.isArmed()) {
                    state = TMSchema$State.CHECKEDPRESSED;
                } else if (model.isRollover()) {
                    state = TMSchema$State.CHECKEDHOT;
                }
            } else {
                state = TMSchema$State.UNCHECKEDNORMAL;
                if (!model.isEnabled()) {
                    state = TMSchema$State.UNCHECKEDDISABLED;
                } else if (model.isPressed() && model.isArmed()) {
                    state = TMSchema$State.UNCHECKEDPRESSED;
                } else if (model.isRollover()) {
                    state = TMSchema$State.UNCHECKEDHOT;
                }
            }
            skin.paintSkin(g, x, y, state);
        } else {
            if ((model.isPressed() && model.isArmed()) || !model.isEnabled()) {
                g.setColor(UIManager.getColor("RadioButton.background"));
            } else {
                g.setColor(UIManager.getColor("RadioButton.interiorBackground"));
            }
            g.fillRect(x + 2, y + 2, 8, 8);
            g.setColor(UIManager.getColor("RadioButton.shadow"));
            g.drawLine(x + 4, y + 0, x + 7, y + 0);
            g.drawLine(x + 2, y + 1, x + 3, y + 1);
            g.drawLine(x + 8, y + 1, x + 9, y + 1);
            g.drawLine(x + 1, y + 2, x + 1, y + 3);
            g.drawLine(x + 0, y + 4, x + 0, y + 7);
            g.drawLine(x + 1, y + 8, x + 1, y + 9);
            g.setColor(UIManager.getColor("RadioButton.highlight"));
            g.drawLine(x + 2, y + 10, x + 3, y + 10);
            g.drawLine(x + 4, y + 11, x + 7, y + 11);
            g.drawLine(x + 8, y + 10, x + 9, y + 10);
            g.drawLine(x + 10, y + 9, x + 10, y + 8);
            g.drawLine(x + 11, y + 7, x + 11, y + 4);
            g.drawLine(x + 10, y + 3, x + 10, y + 2);
            g.setColor(UIManager.getColor("RadioButton.darkShadow"));
            g.drawLine(x + 4, y + 1, x + 7, y + 1);
            g.drawLine(x + 2, y + 2, x + 3, y + 2);
            g.drawLine(x + 8, y + 2, x + 9, y + 2);
            g.drawLine(x + 2, y + 3, x + 2, y + 3);
            g.drawLine(x + 1, y + 4, x + 1, y + 7);
            g.drawLine(x + 2, y + 8, x + 2, y + 8);
            g.setColor(UIManager.getColor("RadioButton.light"));
            g.drawLine(x + 2, y + 9, x + 3, y + 9);
            g.drawLine(x + 4, y + 10, x + 7, y + 10);
            g.drawLine(x + 8, y + 9, x + 9, y + 9);
            g.drawLine(x + 9, y + 8, x + 9, y + 8);
            g.drawLine(x + 10, y + 7, x + 10, y + 4);
            g.drawLine(x + 9, y + 3, x + 9, y + 3);
            if (model.isSelected()) {
                g.setColor(UIManager.getColor("RadioButton.darkShadow"));
                g.fillRect(x + 4, y + 5, 4, 2);
                g.fillRect(x + 5, y + 4, 2, 4);
            }
        }
    }
    
    public int getIconWidth() {
        XPStyle xp = XPStyle.getXP();
        if (xp != null) {
            return xp.getSkin(null, TMSchema$Part.BP_RADIOBUTTON).getWidth();
        } else {
            return 13;
        }
    }
    
    public int getIconHeight() {
        XPStyle xp = XPStyle.getXP();
        if (xp != null) {
            return xp.getSkin(null, TMSchema$Part.BP_RADIOBUTTON).getHeight();
        } else {
            return 13;
        }
    }
}
