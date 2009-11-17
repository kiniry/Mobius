package com.sun.java.swing.plaf.windows;

import javax.swing.plaf.basic.*;
import javax.swing.*;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;
import com.sun.java.swing.plaf.windows.XPStyle.*;

class WindowsMenuBarUI$1 extends WindowAdapter {
    /*synthetic*/ final WindowsMenuBarUI this$0;
    
    WindowsMenuBarUI$1(/*synthetic*/ final WindowsMenuBarUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public void windowActivated(WindowEvent e) {
        WindowsMenuBarUI.access$000(this$0).repaint();
    }
    
    public void windowDeactivated(WindowEvent e) {
        WindowsMenuBarUI.access$100(this$0).repaint();
    }
}
