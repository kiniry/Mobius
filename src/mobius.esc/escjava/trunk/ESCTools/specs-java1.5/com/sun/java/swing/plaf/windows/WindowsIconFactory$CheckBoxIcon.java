package com.sun.java.swing.plaf.windows;

import javax.swing.*;
import java.awt.*;
import java.io.Serializable;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class WindowsIconFactory$CheckBoxIcon implements Icon, Serializable {
    
    /*synthetic*/ WindowsIconFactory$CheckBoxIcon(com.sun.java.swing.plaf.windows.WindowsIconFactory$1 x0) {
        this();
    }
    
    private WindowsIconFactory$CheckBoxIcon() {
        
    }
    static final int csize = 13;
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        JCheckBox cb = (JCheckBox)(JCheckBox)c;
        ButtonModel model = cb.getModel();
        XPStyle xp = XPStyle.getXP();
        if (xp != null) {
            TMSchema$State state;
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
            TMSchema$Part part = TMSchema$Part.BP_CHECKBOX;
            xp.getSkin(c, part).paintSkin(g, x, y, state);
        } else {
            if (!cb.isBorderPaintedFlat()) {
                g.setColor(UIManager.getColor("CheckBox.shadow"));
                g.drawLine(x, y, x + 11, y);
                g.drawLine(x, y + 1, x, y + 11);
                g.setColor(UIManager.getColor("CheckBox.highlight"));
                g.drawLine(x + 12, y, x + 12, y + 12);
                g.drawLine(x, y + 12, x + 11, y + 12);
                g.setColor(UIManager.getColor("CheckBox.darkShadow"));
                g.drawLine(x + 1, y + 1, x + 10, y + 1);
                g.drawLine(x + 1, y + 2, x + 1, y + 10);
                g.setColor(UIManager.getColor("CheckBox.light"));
                g.drawLine(x + 1, y + 11, x + 11, y + 11);
                g.drawLine(x + 11, y + 1, x + 11, y + 10);
                if ((model.isPressed() && model.isArmed()) || !model.isEnabled()) {
                    g.setColor(UIManager.getColor("CheckBox.background"));
                } else {
                    g.setColor(UIManager.getColor("CheckBox.interiorBackground"));
                }
                g.fillRect(x + 2, y + 2, csize - 4, csize - 4);
            } else {
                g.setColor(UIManager.getColor("CheckBox.shadow"));
                g.drawRect(x + 1, y + 1, csize - 3, csize - 3);
                if ((model.isPressed() && model.isArmed()) || !model.isEnabled()) {
                    g.setColor(UIManager.getColor("CheckBox.background"));
                } else {
                    g.setColor(UIManager.getColor("CheckBox.interiorBackground"));
                }
                g.fillRect(x + 2, y + 2, csize - 4, csize - 4);
            }
            if (model.isEnabled()) {
                g.setColor(UIManager.getColor("CheckBox.darkShadow"));
            } else {
                g.setColor(UIManager.getColor("CheckBox.shadow"));
            }
            if (model.isSelected()) {
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
    }
    
    public int getIconWidth() {
        XPStyle xp = XPStyle.getXP();
        if (xp != null) {
            return xp.getSkin(null, TMSchema$Part.BP_CHECKBOX).getWidth();
        } else {
            return csize;
        }
    }
    
    public int getIconHeight() {
        XPStyle xp = XPStyle.getXP();
        if (xp != null) {
            return xp.getSkin(null, TMSchema$Part.BP_CHECKBOX).getHeight();
        } else {
            return csize;
        }
    }
}
