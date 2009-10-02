package com.sun.java.swing.plaf.windows;

import javax.swing.*;
import java.awt.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;
import sun.swing.MenuItemCheckIconFactory;

class WindowsIconFactory$VistaMenuItemCheckIconFactory implements MenuItemCheckIconFactory {
    
    /*synthetic*/ static Class access$1100(String x0) {
        return getType(x0);
    }
    
    /*synthetic*/ static Class access$1000(Component x0) {
        return getType(x0);
    }
    
    WindowsIconFactory$VistaMenuItemCheckIconFactory() {
        
    }
    private static final int OFFSET = 3;
    
    public Icon getIcon(JMenuItem component) {
        return new WindowsIconFactory$VistaMenuItemCheckIconFactory$VistaMenuItemCheckIcon(component);
    }
    
    public boolean isCompatible(Object icon, String prefix) {
        return icon instanceof WindowsIconFactory$VistaMenuItemCheckIconFactory$VistaMenuItemCheckIcon && WindowsIconFactory.VistaMenuItemCheckIconFactory.VistaMenuItemCheckIcon.access$900(((WindowsIconFactory$VistaMenuItemCheckIconFactory$VistaMenuItemCheckIcon)(WindowsIconFactory$VistaMenuItemCheckIconFactory$VistaMenuItemCheckIcon)icon)) == getType(prefix);
    }
    
    public Icon getIcon(String type) {
        return new WindowsIconFactory$VistaMenuItemCheckIconFactory$VistaMenuItemCheckIcon(type);
    }
    
    static int getIconWidth() {
        return XPStyle.getXP().getSkin(null, TMSchema$Part.MP_POPUPCHECK).getWidth() + 2 * OFFSET;
    }
    
    private static Class getType(Component c) {
        Class rv = null;
        if (c instanceof JCheckBoxMenuItem) {
            rv = JCheckBoxMenuItem.class;
        } else if (c instanceof JRadioButtonMenuItem) {
            rv = JRadioButtonMenuItem.class;
        } else if (c instanceof JMenu) {
            rv = JMenu.class;
        } else if (c instanceof JMenuItem) {
            rv = JMenuItem.class;
        }
        return rv;
    }
    
    private static Class getType(String type) {
        Class rv = null;
        if (type == "CheckBoxMenuItem") {
            rv = JCheckBoxMenuItem.class;
        } else if (type == "RadioButtonMenuItem") {
            rv = JRadioButtonMenuItem.class;
        } else if (type == "Menu") {
            rv = JMenu.class;
        } else if (type == "MenuItem") {
            rv = JMenuItem.class;
        } else {
            rv = JMenuItem.class;
        }
        return rv;
    }
    {
    }
}
