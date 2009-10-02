package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;

public class WindowsCheckBoxMenuItemUI extends BasicCheckBoxMenuItemUI {
    
    /*synthetic*/ static JMenuItem access$000(WindowsCheckBoxMenuItemUI x0) {
        return x0.menuItem;
    }
    
    public WindowsCheckBoxMenuItemUI() {
        
    }
    final WindowsMenuItemUIAccessor accessor = new WindowsCheckBoxMenuItemUI$1(this);
    
    public static ComponentUI createUI(JComponent b) {
        return new WindowsCheckBoxMenuItemUI();
    }
    
    @Override()
    protected void paintBackground(Graphics g, JMenuItem menuItem, Color bgColor) {
        if (WindowsMenuItemUI.isVistaPainting()) {
            WindowsMenuItemUI.paintBackground(accessor, g, menuItem, bgColor);
            return;
        }
        super.paintBackground(g, menuItem, bgColor);
    }
    
    protected void paintText(Graphics g, JMenuItem menuItem, Rectangle textRect, String text) {
        if (WindowsMenuItemUI.isVistaPainting()) {
            WindowsMenuItemUI.paintText(accessor, g, menuItem, textRect, text);
            return;
        }
        ButtonModel model = menuItem.getModel();
        Color oldColor = g.getColor();
        if (model.isEnabled() && model.isArmed()) {
            g.setColor(selectionForeground);
        }
        WindowsGraphicsUtils.paintText(g, menuItem, textRect, text, 0);
        g.setColor(oldColor);
    }
}
