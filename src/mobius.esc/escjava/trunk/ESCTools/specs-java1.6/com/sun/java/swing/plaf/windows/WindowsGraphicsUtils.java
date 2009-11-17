package com.sun.java.swing.plaf.windows;

import com.sun.java.swing.SwingUtilities2;
import java.awt.*;
import javax.swing.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;

public class WindowsGraphicsUtils {
    
    public WindowsGraphicsUtils() {
        
    }
    
    public static void paintText(Graphics g, AbstractButton b, Rectangle textRect, String text, int textShiftOffset) {
        ButtonModel model = b.getModel();
        FontMetrics fm = SwingUtilities2.getFontMetrics(b, g);
        int mnemIndex = b.getDisplayedMnemonicIndex();
        if (WindowsLookAndFeel.isMnemonicHidden() == true) {
            mnemIndex = -1;
        }
        Color color = b.getForeground();
        if (model.isEnabled()) {
            if (!(b instanceof JMenuItem && model.isArmed()) && !(b instanceof JMenu && (model.isSelected() || model.isRollover()))) {
                g.setColor(b.getForeground());
            }
            SwingUtilities2.drawStringUnderlineCharAt(b, g, text, mnemIndex, textRect.x + textShiftOffset, textRect.y + fm.getAscent() + textShiftOffset);
        } else {
            color = UIManager.getColor("Button.disabledForeground");
            Color shadow = UIManager.getColor("Button.disabledShadow");
            XPStyle xp = XPStyle.getXP();
            if (xp != null) {
                TMSchema$Part part = WindowsButtonUI.getXPButtonType(b);
                color = xp.getColor(b, part, TMSchema$State.DISABLED, TMSchema$Prop.TEXTCOLOR, color);
                if (part == TMSchema$Part.TP_BUTTON) {
                    Color enabledColor = xp.getColor(b, part, TMSchema$State.NORMAL, TMSchema$Prop.TEXTCOLOR, color);
                    if (color != null && color.equals(enabledColor)) {
                        color = xp.getColor(b, TMSchema$Part.TP_BUTTON, TMSchema$State.DISABLED, TMSchema$Prop.TEXTCOLOR, color);
                    }
                }
            } else {
                if (shadow == null) {
                    shadow = b.getBackground().darker();
                }
                g.setColor(shadow);
                SwingUtilities2.drawStringUnderlineCharAt(b, g, text, mnemIndex, textRect.x, textRect.y + fm.getAscent());
            }
            if (color == null) {
                color = b.getBackground().brighter();
            }
            g.setColor(color);
            SwingUtilities2.drawStringUnderlineCharAt(b, g, text, mnemIndex, textRect.x - 1, textRect.y + fm.getAscent() - 1);
        }
    }
    
    static boolean isLeftToRight(Component c) {
        return c.getComponentOrientation().isLeftToRight();
    }
}
