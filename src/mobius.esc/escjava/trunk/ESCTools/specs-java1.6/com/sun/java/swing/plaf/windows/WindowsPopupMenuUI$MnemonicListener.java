package com.sun.java.swing.plaf.windows;

import java.awt.Component;
import java.awt.Window;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;

class WindowsPopupMenuUI$MnemonicListener implements ChangeListener {
    
    WindowsPopupMenuUI$MnemonicListener() {
        
    }
    JRootPane repaintRoot = null;
    
    public void stateChanged(ChangeEvent ev) {
        MenuSelectionManager msm = (MenuSelectionManager)(MenuSelectionManager)ev.getSource();
        MenuElement[] path = msm.getSelectedPath();
        if (path.length == 0) {
            if (!WindowsLookAndFeel.isMnemonicHidden()) {
                WindowsLookAndFeel.setMnemonicHidden(true);
                if (repaintRoot != null) {
                    Window win = SwingUtilities.getWindowAncestor(repaintRoot);
                    WindowsUtils.repaintMnemonicsInWindow(win);
                }
            }
        } else {
            Component c = (Component)(Component)path[0];
            if (c instanceof JPopupMenu) c = ((JPopupMenu)(JPopupMenu)c).getInvoker();
            repaintRoot = SwingUtilities.getRootPane(c);
        }
    }
}
