package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.plaf.ComponentUI;
import javax.swing.plaf.basic.BasicMenuUI;
import javax.swing.event.MouseInputListener;
import javax.swing.*;

public class WindowsMenuUI extends BasicMenuUI {
    
    /*synthetic*/ static JMenuItem access$200(WindowsMenuUI x0) {
        return x0.menuItem;
    }
    
    /*synthetic*/ static JMenuItem access$100(WindowsMenuUI x0) {
        return x0.menuItem;
    }
    
    /*synthetic*/ static JMenuItem access$000(WindowsMenuUI x0) {
        return x0.menuItem;
    }
    
    public WindowsMenuUI() {
        
    }
    final WindowsMenuItemUIAccessor accessor = new WindowsMenuUI$1(this);
    
    public static ComponentUI createUI(JComponent x) {
        return new WindowsMenuUI();
    }
    
    protected void installDefaults() {
        super.installDefaults();
        if (!WindowsLookAndFeel.isClassicWindows()) {
            menuItem.setRolloverEnabled(true);
        }
    }
    
    protected void paintBackground(Graphics g, JMenuItem menuItem, Color bgColor) {
        if (WindowsMenuItemUI.isVistaPainting()) {
            WindowsMenuItemUI.paintBackground(accessor, g, menuItem, bgColor);
            return;
        }
        JMenu menu = (JMenu)(JMenu)menuItem;
        ButtonModel model = menu.getModel();
        if (WindowsLookAndFeel.isClassicWindows() || !menu.isTopLevelMenu() || (XPStyle.getXP() != null && (model.isArmed() || model.isSelected()))) {
            super.paintBackground(g, menu, bgColor);
            return;
        }
        Color oldColor = g.getColor();
        int menuWidth = menu.getWidth();
        int menuHeight = menu.getHeight();
        UIDefaults table = UIManager.getLookAndFeelDefaults();
        Color highlight = table.getColor("controlLtHighlight");
        Color shadow = table.getColor("controlShadow");
        g.setColor(menu.getBackground());
        g.fillRect(0, 0, menuWidth, menuHeight);
        if (menu.isOpaque()) {
            if (model.isArmed() || model.isSelected()) {
                g.setColor(shadow);
                g.drawLine(0, 0, menuWidth - 1, 0);
                g.drawLine(0, 0, 0, menuHeight - 2);
                g.setColor(highlight);
                g.drawLine(menuWidth - 1, 0, menuWidth - 1, menuHeight - 2);
                g.drawLine(0, menuHeight - 2, menuWidth - 1, menuHeight - 2);
            } else if (model.isRollover() && model.isEnabled()) {
                boolean otherMenuSelected = false;
                MenuElement[] menus = ((JMenuBar)(JMenuBar)menu.getParent()).getSubElements();
                for (int i = 0; i < menus.length; i++) {
                    if (((JMenuItem)(JMenuItem)menus[i]).isSelected()) {
                        otherMenuSelected = true;
                        break;
                    }
                }
                if (!otherMenuSelected) {
                    if (XPStyle.getXP() != null) {
                        g.setColor(selectionBackground);
                        g.fillRect(0, 0, menuWidth, menuHeight);
                    } else {
                        g.setColor(highlight);
                        g.drawLine(0, 0, menuWidth - 1, 0);
                        g.drawLine(0, 0, 0, menuHeight - 2);
                        g.setColor(shadow);
                        g.drawLine(menuWidth - 1, 0, menuWidth - 1, menuHeight - 2);
                        g.drawLine(0, menuHeight - 2, menuWidth - 1, menuHeight - 2);
                    }
                }
            }
        }
        g.setColor(oldColor);
    }
    
    protected void paintText(Graphics g, JMenuItem menuItem, Rectangle textRect, String text) {
        if (WindowsMenuItemUI.isVistaPainting()) {
            WindowsMenuItemUI.paintText(accessor, g, menuItem, textRect, text);
            return;
        }
        JMenu menu = (JMenu)(JMenu)menuItem;
        ButtonModel model = menuItem.getModel();
        Color oldColor = g.getColor();
        boolean paintRollover = model.isRollover();
        if (paintRollover && menu.isTopLevelMenu()) {
            MenuElement[] menus = ((JMenuBar)(JMenuBar)menu.getParent()).getSubElements();
            for (int i = 0; i < menus.length; i++) {
                if (((JMenuItem)(JMenuItem)menus[i]).isSelected()) {
                    paintRollover = false;
                    break;
                }
            }
        }
        if ((model.isSelected() && (WindowsLookAndFeel.isClassicWindows() || !menu.isTopLevelMenu())) || (XPStyle.getXP() != null && (paintRollover || model.isArmed() || model.isSelected()))) {
            g.setColor(selectionForeground);
        }
        WindowsGraphicsUtils.paintText(g, menuItem, textRect, text, 0);
        g.setColor(oldColor);
    }
    
    protected MouseInputListener createMouseInputListener(JComponent c) {
        return new WindowsMenuUI$WindowsMouseInputHandler(this);
    }
    {
    }
}
