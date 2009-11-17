package com.sun.java.swing.plaf.windows;

import javax.swing.plaf.basic.*;
import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;
import com.sun.java.swing.plaf.windows.XPStyle.*;

class WindowsMenuBarUI$TakeFocus extends AbstractAction {
    
    /*synthetic*/ WindowsMenuBarUI$TakeFocus(com.sun.java.swing.plaf.windows.WindowsMenuBarUI$1 x0) {
        this();
    }
    
    private WindowsMenuBarUI$TakeFocus() {
        
    }
    
    public void actionPerformed(ActionEvent e) {
        JMenuBar menuBar = (JMenuBar)(JMenuBar)e.getSource();
        JMenu menu = menuBar.getMenu(0);
        if (menu != null) {
            MenuSelectionManager msm = MenuSelectionManager.defaultManager();
            MenuElement[] path = new MenuElement[2];
            path[0] = (MenuElement)menuBar;
            path[1] = (MenuElement)menu;
            msm.setSelectedPath(path);
            WindowsLookAndFeel.setMnemonicHidden(false);
            WindowsLookAndFeel.repaintRootPane(menuBar);
        }
    }
}
