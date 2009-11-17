package com.sun.java.swing.plaf.windows;

import javax.swing.plaf.basic.*;
import javax.swing.*;
import java.awt.event.HierarchyEvent;
import java.awt.event.HierarchyListener;
import java.awt.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;
import com.sun.java.swing.plaf.windows.XPStyle.*;

class WindowsMenuBarUI$2 implements HierarchyListener {
    /*synthetic*/ final WindowsMenuBarUI this$0;
    
    WindowsMenuBarUI$2(/*synthetic*/ final WindowsMenuBarUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void hierarchyChanged(HierarchyEvent e) {
        if ((e.getChangeFlags() & HierarchyEvent.DISPLAYABILITY_CHANGED) != 0) {
            if (WindowsMenuBarUI.access$200(this$0).isDisplayable()) {
                WindowsMenuBarUI.access$300(this$0);
            } else {
                WindowsMenuBarUI.access$400(this$0);
            }
        }
    }
}
