package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import com.sun.java.swing.SwingUtilities2;
import com.sun.java.swing.plaf.windows.TMSchema.*;
import com.sun.java.swing.plaf.windows.XPStyle.*;

public class WindowsMenuItemUI extends BasicMenuItemUI {
    
    /*synthetic*/ static JMenuItem access$000(WindowsMenuItemUI x0) {
        return x0.menuItem;
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !WindowsMenuItemUI.class.desiredAssertionStatus();
    
    public WindowsMenuItemUI() {
        
    }
    final WindowsMenuItemUIAccessor accessor = new WindowsMenuItemUI$1(this);
    
    public static ComponentUI createUI(JComponent c) {
        return new WindowsMenuItemUI();
    }
    
    protected void paintText(Graphics g, JMenuItem menuItem, Rectangle textRect, String text) {
        if (WindowsMenuItemUI.isVistaPainting()) {
            WindowsMenuItemUI.paintText(accessor, g, menuItem, textRect, text);
            return;
        }
        ButtonModel model = menuItem.getModel();
        Color oldColor = g.getColor();
        if (model.isEnabled() && (model.isArmed() || (menuItem instanceof JMenu && model.isSelected()))) {
            g.setColor(selectionForeground);
        }
        WindowsGraphicsUtils.paintText(g, menuItem, textRect, text, 0);
        g.setColor(oldColor);
    }
    
    @Override()
    protected void paintBackground(Graphics g, JMenuItem menuItem, Color bgColor) {
        if (WindowsMenuItemUI.isVistaPainting()) {
            WindowsMenuItemUI.paintBackground(accessor, g, menuItem, bgColor);
            return;
        }
        super.paintBackground(g, menuItem, bgColor);
    }
    
    static void paintBackground(WindowsMenuItemUIAccessor menuItemUI, Graphics g, JMenuItem menuItem, Color bgColor) {
        if (!$assertionsDisabled && !isVistaPainting()) throw new AssertionError();
        if (isVistaPainting()) {
            int menuWidth = menuItem.getWidth();
            int menuHeight = menuItem.getHeight();
            if (menuItem.isOpaque()) {
                Color oldColor = g.getColor();
                g.setColor(menuItem.getBackground());
                g.fillRect(0, 0, menuWidth, menuHeight);
                g.setColor(oldColor);
            }
            XPStyle xp = XPStyle.getXP();
            TMSchema$Part part = menuItemUI.getPart(menuItem);
            XPStyle$Skin skin = xp.getSkin(menuItem, part);
            skin.paintSkin(g, 0, 0, menuWidth, menuHeight, menuItemUI.getState(menuItem));
        }
    }
    
    static void paintText(WindowsMenuItemUIAccessor menuItemUI, Graphics g, JMenuItem menuItem, Rectangle textRect, String text) {
        if (!$assertionsDisabled && !isVistaPainting()) throw new AssertionError();
        if (isVistaPainting()) {
            TMSchema$State state = menuItemUI.getState(menuItem);
            FontMetrics fm = SwingUtilities2.getFontMetrics(menuItem, g);
            int mnemIndex = menuItem.getDisplayedMnemonicIndex();
            if (WindowsLookAndFeel.isMnemonicHidden() == true) {
                mnemIndex = -1;
            }
            XPStyle xp = XPStyle.getXP();
            Color textColor = menuItem.getForeground();
            if (textColor instanceof UIResource) {
                TMSchema$Part part = menuItemUI.getPart(menuItem);
                textColor = xp.getColor(menuItem, part, state, TMSchema$Prop.TEXTCOLOR, textColor);
            }
            g.setColor(textColor);
            SwingUtilities2.drawStringUnderlineCharAt(menuItem, g, text, mnemIndex, textRect.x, textRect.y + fm.getAscent());
        }
    }
    
    static TMSchema$State getState(WindowsMenuItemUIAccessor menuItemUI, JMenuItem menuItem) {
        TMSchema$State state;
        ButtonModel model = menuItem.getModel();
        if (model.isArmed()) {
            state = (model.isEnabled()) ? TMSchema$State.HOT : TMSchema$State.DISABLEDHOT;
        } else {
            state = (model.isEnabled()) ? TMSchema$State.NORMAL : TMSchema$State.DISABLED;
        }
        return state;
    }
    
    static TMSchema$Part getPart(WindowsMenuItemUIAccessor menuItemUI, JMenuItem menuItem) {
        return TMSchema$Part.MP_POPUPITEM;
    }
    
    static boolean isVistaPainting() {
        XPStyle xp = XPStyle.getXP();
        return xp != null && xp.isSkinDefined(null, TMSchema$Part.MP_POPUPITEM);
    }
}
