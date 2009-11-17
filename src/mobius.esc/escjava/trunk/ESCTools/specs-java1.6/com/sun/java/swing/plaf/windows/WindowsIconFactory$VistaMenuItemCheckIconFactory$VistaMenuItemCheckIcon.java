package com.sun.java.swing.plaf.windows;

import javax.swing.*;
import javax.swing.plaf.ButtonUI;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;
import com.sun.java.swing.plaf.windows.TMSchema.*;
import com.sun.java.swing.plaf.windows.XPStyle.Skin;

class WindowsIconFactory$VistaMenuItemCheckIconFactory$VistaMenuItemCheckIcon implements Icon, UIResource, Serializable {
    
    /*synthetic*/ static Class access$900(WindowsIconFactory$VistaMenuItemCheckIconFactory$VistaMenuItemCheckIcon x0) {
        return x0.type;
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !WindowsIconFactory.class.desiredAssertionStatus();
    private final JMenuItem menuItem;
    private final Class type;
    
    WindowsIconFactory$VistaMenuItemCheckIconFactory$VistaMenuItemCheckIcon(JMenuItem menuItem) {
        
        this.type = WindowsIconFactory.VistaMenuItemCheckIconFactory.access$1000(menuItem);
        this.menuItem = menuItem;
    }
    
    WindowsIconFactory$VistaMenuItemCheckIconFactory$VistaMenuItemCheckIcon(String type) {
        
        this.type = WindowsIconFactory.VistaMenuItemCheckIconFactory.access$1100(type);
        this.menuItem = null;
    }
    
    public int getIconHeight() {
        Icon lafIcon = getLaFIcon();
        if (lafIcon != null) {
            return lafIcon.getIconHeight();
        }
        Icon icon = getIcon();
        int height = 0;
        if (icon != null) {
            height = icon.getIconHeight() + 2 * 3;
        } else {
            XPStyle$Skin skin = XPStyle.getXP().getSkin(null, TMSchema$Part.MP_POPUPCHECK);
            height = skin.getHeight() + 2 * 3;
        }
        return height;
    }
    
    public int getIconWidth() {
        Icon lafIcon = getLaFIcon();
        if (lafIcon != null) {
            return lafIcon.getIconWidth();
        }
        Icon icon = getIcon();
        int width = 0;
        if (icon != null) {
            width = icon.getIconWidth() + 2 * 3;
        } else {
            width = WindowsIconFactory$VistaMenuItemCheckIconFactory.getIconWidth();
        }
        return width;
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        Icon lafIcon = getLaFIcon();
        if (lafIcon != null) {
            lafIcon.paintIcon(c, g, x, y);
            return;
        }
        if (!$assertionsDisabled && !(menuItem == null || c == menuItem)) throw new AssertionError();
        Icon icon = getIcon();
        if (type == JCheckBoxMenuItem.class || type == JRadioButtonMenuItem.class) {
            AbstractButton b = (AbstractButton)(AbstractButton)c;
            if (b.isSelected()) {
                TMSchema$Part backgroundPart = TMSchema$Part.MP_POPUPCHECKBACKGROUND;
                TMSchema$Part part = TMSchema$Part.MP_POPUPCHECK;
                TMSchema$State backgroundState;
                TMSchema$State state;
                if (isEnabled(c, null)) {
                    backgroundState = (icon != null) ? TMSchema$State.BITMAP : TMSchema$State.NORMAL;
                    state = (type == JRadioButtonMenuItem.class) ? TMSchema$State.BULLETNORMAL : TMSchema$State.CHECKMARKNORMAL;
                } else {
                    backgroundState = TMSchema$State.DISABLEDPUSHED;
                    state = (type == JRadioButtonMenuItem.class) ? TMSchema$State.BULLETDISABLED : TMSchema$State.CHECKMARKDISABLED;
                }
                XPStyle$Skin skin;
                XPStyle xp = XPStyle.getXP();
                skin = xp.getSkin(c, backgroundPart);
                skin.paintSkin(g, x, y, getIconWidth(), getIconHeight(), backgroundState);
                if (icon == null) {
                    skin = xp.getSkin(c, part);
                    skin.paintSkin(g, x + 3, y + 3, state);
                }
            }
        }
        if (icon != null) {
            icon.paintIcon(c, g, x + 3, y + 3);
        }
    }
    
    private static WindowsMenuItemUIAccessor getAccessor(JMenuItem menuItem) {
        WindowsMenuItemUIAccessor rv = null;
        ButtonUI uiObject = (menuItem != null) ? menuItem.getUI() : null;
        if (uiObject instanceof WindowsMenuItemUI) {
            rv = ((WindowsMenuItemUI)(WindowsMenuItemUI)uiObject).accessor;
        } else if (uiObject instanceof WindowsMenuUI) {
            rv = ((WindowsMenuUI)(WindowsMenuUI)uiObject).accessor;
        } else if (uiObject instanceof WindowsCheckBoxMenuItemUI) {
            rv = ((WindowsCheckBoxMenuItemUI)(WindowsCheckBoxMenuItemUI)uiObject).accessor;
        } else if (uiObject instanceof WindowsRadioButtonMenuItemUI) {
            rv = ((WindowsRadioButtonMenuItemUI)(WindowsRadioButtonMenuItemUI)uiObject).accessor;
        }
        return rv;
    }
    
    private static boolean isEnabled(Component c, TMSchema$State state) {
        if (state == null && c instanceof JMenuItem) {
            WindowsMenuItemUIAccessor accessor = getAccessor((JMenuItem)(JMenuItem)c);
            if (accessor != null) {
                state = accessor.getState((JMenuItem)(JMenuItem)c);
            }
        }
        if (state == null) {
            if (c != null) {
                return c.isEnabled();
            } else {
                return true;
            }
        } else {
            return (state != TMSchema$State.DISABLED) && (state != TMSchema$State.DISABLEDHOT) && (state != TMSchema$State.DISABLEDPUSHED);
        }
    }
    
    private Icon getIcon() {
        Icon rv = null;
        if (menuItem == null) {
            return rv;
        }
        WindowsMenuItemUIAccessor accessor = getAccessor(menuItem);
        TMSchema$State state = (accessor != null) ? accessor.getState(menuItem) : null;
        if (isEnabled(menuItem, null)) {
            if (state == TMSchema$State.PUSHED) {
                rv = menuItem.getPressedIcon();
            } else {
                rv = menuItem.getIcon();
            }
        } else {
            rv = menuItem.getDisabledIcon();
        }
        return rv;
    }
    
    private Icon getLaFIcon() {
        Icon rv = (Icon)(Icon)UIManager.getDefaults().get(typeToString(type));
        if (rv instanceof WindowsIconFactory$VistaMenuItemCheckIconFactory$VistaMenuItemCheckIcon && ((WindowsIconFactory$VistaMenuItemCheckIconFactory$VistaMenuItemCheckIcon)(WindowsIconFactory$VistaMenuItemCheckIconFactory$VistaMenuItemCheckIcon)rv).type == type) {
            rv = null;
        }
        return rv;
    }
    
    private static String typeToString(Class type) {
        if (!$assertionsDisabled && !(type == JMenuItem.class || type == JMenu.class || type == JCheckBoxMenuItem.class || type == JRadioButtonMenuItem.class)) throw new AssertionError();
        StringBuilder sb = new StringBuilder(type.getName());
        sb.delete(0, sb.lastIndexOf("J") + 1);
        sb.append(".checkIcon");
        return sb.toString();
    }
}
